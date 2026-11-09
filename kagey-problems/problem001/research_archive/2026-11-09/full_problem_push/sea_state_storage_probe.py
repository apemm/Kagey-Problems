"""Read a bounded checkpoint prefix and measure exact block interning costs.

This does not resume a graph search or modify a checkpoint. The dictionary
estimates use packed keys and four-byte identifiers, not Python object sizes.
"""
import argparse
import collections
import json
from pathlib import Path
import struct
import time


def decode(data):
    expected = int.from_bytes(data[:2], 'little')
    value = previous = delta = shift = count = 0
    for byte in data[2:]:
        delta |= (byte & 127) << shift
        if byte & 128:
            shift += 7
        else:
            previous += delta
            value |= 1 << previous
            delta = shift = 0
            count += 1
    assert shift == 0 and count == expected and value.bit_count() == count
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('checkpoint', type=Path)
    parser.add_argument('--states', type=int, default=50000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    states = []
    lengths = []
    with args.checkpoint.open('rb') as stream:
        magic, height, words, total, processed, edges = struct.unpack('<6i', stream.read(24))
        assert magic == 0x53454133, hex(magic)
        for _ in range(min(total, args.states)):
            length, = struct.unpack('<i', stream.read(4))
            data = stream.read(length)
            assert len(data) == length
            lengths.append(length)
            states.append(decode(data))
    sample = len(states)
    results = []
    for bits in (64, 128, 256, 512):
        width = (64 * words + bits - 1) // bits
        mask = (1 << bits) - 1
        unique = set()
        nonzero = 0
        for state in states:
            for _ in range(width):
                block = state & mask
                unique.add(block)
                nonzero += block != 0
                state >>= bits
        # Global shared pool: fixed-width block payload plus a four-byte
        # open-addressing slot at load 0.75. Per-state dense identifier vector.
        pool = len(unique) * (bits / 8 + 4 / .75)
        results.append(dict(block_bits=bits, blocks_per_state=width,
                            unique_blocks=len(unique), nonzero_blocks=nonzero,
                            packed_id_bytes_per_state=4*width,
                            estimated_pool_bytes=pool,
                            estimated_total_bytes_per_state=4*width+pool/sample))
    output = dict(checkpoint=args.checkpoint.name, height=height,
                  residual_words=words, total_states=total,
                  processed_states=processed, sample_states=sample,
                  sample_kind='initial BFS prefix; not an extrapolation',
                  average_sparse_payload_bytes=sum(lengths)/sample,
                  average_live_residuals=sum(x.bit_count() for x in states)/sample,
                  lengths=dict(collections.Counter(lengths)),
                  exact_block_estimates=results, seconds=time.monotonic()-start)
    text = json.dumps(output, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(json.dumps({key:value for key,value in output.items() if key != 'lengths'}))


if __name__ == '__main__':
    main()
