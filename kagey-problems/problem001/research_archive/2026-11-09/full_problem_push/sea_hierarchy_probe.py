"""Bounded exact compression measurements on packed-state checkpoint samples.

No graph enumeration and no checkpoint mutation. NumPy unique compares the
complete pair or block key. Every hierarchy level is round-trip checked.
"""
from __future__ import annotations
import argparse
import ctypes
import json
import math
from pathlib import Path
import struct
import time
import numpy as np


def peak_mb():
    class Counters(ctypes.Structure):
        _fields_ = [("cb", ctypes.c_ulong), ("PageFaultCount", ctypes.c_ulong)] + [
            (name, ctypes.c_size_t) for name in (
                "PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage",
                "QuotaPagedPoolUsage", "QuotaPeakNonPagedPoolUsage",
                "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage")]
    c = Counters()
    c.cb = ctypes.sizeof(c)
    okay = ctypes.windll.psapi.GetProcessMemoryInfo(
        ctypes.c_void_p(-1), ctypes.byref(c), c.cb)
    assert okay
    return c.PeakWorkingSetSize / 2**20


def table_bytes(n):
    size = 1024
    while n > 0.72 * size:
        size *= 2
    return 4 * size


def run(path, count, mode, seed):
    started = time.perf_counter()
    with path.open("rb") as f:
        magic, h, words = struct.unpack("<3i", f.read(12))
        assert magic == 0x53454134
        fingerprint = f.read(32).hex()
        n, processed, edges, pool = struct.unpack("<4i", f.read(16))
        zero_block = f.read(32)
    width = (words + 3) // 4
    state_start = 60 + 32 * pool
    expected = state_start + 4 * width * n + 8 * n + 4 * edges
    assert expected == path.stat().st_size
    count = min(count, n)
    if mode == "uniform":
        indices = np.linspace(0, n - 1, count, dtype=np.int64)
    elif mode == "random":
        indices = np.sort(np.random.default_rng(seed).choice(n, count, replace=False))
    elif mode == "first":
        indices = np.arange(count)
    elif mode == "middle":
        indices = np.arange(n // 2, n // 2 + count)
    elif mode == "last":
        indices = np.arange(n - count, n)
    else:
        raise ValueError(mode)
    source = np.memmap(path, dtype="<u4", mode="r", offset=state_start,
                       shape=(n, width))
    values = np.array(source[indices], dtype=np.uint32, copy=True)
    del source
    result = dict(checkpoint=path.name, input_sha256=fingerprint, height=h,
                  words=words, width=width, total_states=n, processed=processed,
                  pool_blocks=pool, sample_size=count, sample_mode=mode,
                  flat_id_bytes=int(values.nbytes), zero_block_is_id_zero=not any(zero_block))
    # Position-wise base is a separately stored exact vector. Sparse records
    # need a position byte (width <= 256 here) plus a four-byte replacement ID.
    modes = [np.unique(values[:, j], return_counts=True) for j in range(width)]
    modal = np.array([ids[np.argmax(counts)] for ids, counts in modes], dtype=np.uint32)
    del modes
    differing = (values != modal).sum(axis=1)
    nonzero = np.count_nonzero(values, axis=1)
    runs = 1 + (values[:, 1:] != values[:, :-1]).sum(axis=1)
    result["simple_records"] = dict(
        nonzero_mean=float(nonzero.mean()), modal_differences_mean=float(differing.mean()),
        runs_mean=float(runs.mean()),
        sparse_zero_bytes=float((4 + 5 * nonzero).mean()),
        sparse_modal_bytes=float((4 + 5 * differing).mean()),
        rle_bytes=float((4 + 5 * runs).mean()),
        zero_bitmap_int_ids_bytes=float((math.ceil(width / 8) + 4 * nonzero).mean()),
        zero_bitmap_packed_ids_bytes=float((
            math.ceil(width / 8) + np.ceil(pool.bit_length() * nonzero / 8)).mean()),
        fixed_packed_ids_bytes=math.ceil(width * pool.bit_length() / 8))
    padded = 1 << (width - 1).bit_length()
    current = np.full((count, padded), np.iinfo(np.uint32).max, dtype=np.uint32)
    current[:, :width] = values
    cumulative_nodes = 0
    cumulative_tables = 0
    levels = []
    level = 0
    while current.shape[1] > 1:
        level += 1
        before = current
        pairs = before.reshape(-1, 2)
        unique, inverse = np.unique(pairs, axis=0, return_inverse=True)
        assert np.array_equal(unique[inverse], pairs)
        current = inverse.astype(np.uint32).reshape(count, -1)
        node_count = len(unique)
        cumulative_nodes += 8 * node_count
        cumulative_tables += table_bytes(node_count)
        total = cumulative_nodes + cumulative_tables + current.nbytes
        levels.append(dict(
            depth=level, span=2**level, distinct_nodes=node_count,
            vector_ids_per_state=current.shape[1],
            stored_bytes=int(total), bytes_per_state=float(total / count),
            all_level_keys_and_tables_bytes=cumulative_nodes+cumulative_tables,
            seconds=round(time.perf_counter() - started, 3)))
        del unique, inverse, pairs, before
    assert len(np.unique(current[:, 0])) == count, "Sample contains duplicate states"
    result["binary_hierarchy"] = levels
    # Independent fixed-block interning, without paying for lower levels.
    result["fixed_chunks"] = []
    for size in (2, 3, 4, 6, 8, 12, 16):
        cols = math.ceil(width / size)
        padded_values = np.full((count, cols * size), np.iinfo(np.uint32).max,
                               dtype=np.uint32)
        padded_values[:, :width] = values
        keys = padded_values.reshape(-1, size)
        unique, inverse = np.unique(keys, axis=0, return_inverse=True)
        assert np.array_equal(unique[inverse], keys)
        total = 4 * size * len(unique) + table_bytes(len(unique)) + 4 * cols * count
        result["fixed_chunks"].append(dict(
            span=size, distinct_keys=len(unique), vector_ids_per_state=cols,
            stored_bytes=total, bytes_per_state=total / count))
        del padded_values, keys, unique, inverse
    result["roundtrip_checks"] = "PASS: every complete key reconstructed exactly"
    result["seconds"] = round(time.perf_counter() - started, 3)
    result["peak_working_set_mb"] = round(peak_mb(), 1)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("checkpoint", type=Path)
    ap.add_argument("--count", type=int, default=10000)
    ap.add_argument("--mode", choices=["uniform", "random", "first", "middle", "last"],
                    default="uniform")
    ap.add_argument("--seed", type=int, default=20261109)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    result = run(args.checkpoint, args.count, args.mode, args.seed)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
