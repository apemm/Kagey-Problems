"""Bounded exact MDD experiment for the sparse sea-pattern automaton.

TRUE means unavoidable future failure, so this representation may prune finite
prefixes earlier than the residual-antichain DFA. It preserves the bi-infinite
label shift; recurrent SCCs, not transient state counts, are the comparison.
"""
import argparse
import json
import time
from sea_sparse_automaton import forbidden_patterns, build_graph, scc, resident_bytes


class HazardMDD:
    def __init__(self, h, patterns, deadline, memory_mb):
        self.h = h
        self.deadline = deadline
        self.limit = memory_mb * 2**20
        self.level = [10**9, 10**9]
        self.children = [(), ()]
        self.unique = {}
        self.or_cache = {}
        self.shift_cache = {0: 0, 1: 1}
        self.starts = [0] * (h + 1)
        for pattern in patterns:
            node = 1
            for offset, row in reversed(pattern[1:]):
                children = [0] * h
                children[row - 1] = node
                node = self.make(offset - 1, tuple(children))
            self.starts[pattern[0][1]] = self.union(self.starts[pattern[0][1]], node)

    def make(self, level, children):
        if all(c == children[0] for c in children):
            return children[0]
        key = (level, children)
        old = self.unique.get(key)
        if old is not None:
            return old
        node = len(self.level)
        self.unique[key] = node
        self.level.append(level)
        self.children.append(children)
        if node % 1000 == 0:
            if time.monotonic() > self.deadline:
                raise TimeoutError("MDD construction time cap")
            if resident_bytes() > self.limit:
                raise MemoryError("MDD memory cap")
        return node

    def union(self, a, b):
        if a == b or b == 0:
            return a
        if a == 0 or b == 1:
            return b
        if a == 1:
            return 1
        if a > b:
            a, b = b, a
        key = (a, b)
        old = self.or_cache.get(key)
        if old is not None:
            return old
        la, lb = self.level[a], self.level[b]
        level = min(la, lb)
        ca = self.children[a] if la == level else (a,) * self.h
        cb = self.children[b] if lb == level else (b,) * self.h
        result = self.make(level, tuple(self.union(x, y) for x, y in zip(ca, cb)))
        self.or_cache[key] = result
        return result

    def shift(self, node):
        old = self.shift_cache.get(node)
        if old is not None:
            return old
        assert self.level[node] > 0
        result = self.make(self.level[node] - 1,
                           tuple(self.shift(c) for c in self.children[node]))
        self.shift_cache[node] = result
        return result

    def transition(self, state, letter):
        restricted = (self.children[state][letter - 1]
                      if self.level[state] == 0 else state)
        if restricted == 1:
            return None
        result = self.union(self.shift(restricted), self.starts[letter])
        return None if result == 1 else result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("h", type=int)
    parser.add_argument("--seconds", type=float, default=120)
    parser.add_argument("--memory-mb", type=int, default=512)
    parser.add_argument("--state-cap", type=int, default=1000000)
    args = parser.parse_args()
    start = time.monotonic()
    deadline = start + args.seconds
    output = {"height": args.h, "complete": False}
    mdd = None
    try:
        patterns, stats = forbidden_patterns(args.h, deadline)
        output["patterns"] = stats
        mdd = HazardMDD(args.h, patterns, deadline, args.memory_mb)
        states, trans, complete, details = build_graph(
            mdd.transition, args.h, deadline, args.state_cap, args.memory_mb)
        output.update(details)
        output.update(complete=complete, states=len(states),
                      edges=sum(j >= 0 for j in trans))
        if complete:
            component, sizes, cyclic = scc(trans, args.h)
            output["cyclic_scc_sizes"] = sorted(sizes[c] for c in cyclic)
            output["transient_sccs"] = len(sizes) - len(cyclic)
            # Exploratory numerical check, explicitly not an exact enclosure.
            members = [i for i, c in enumerate(component) if c in cyclic]
            member_set = set(members)
            vector = [1.0 if i in member_set else 0.0 for i in range(len(states))]
            estimate = None
            for _ in range(250):
                if time.monotonic() > deadline:
                    break
                new = [0.0] * len(states)
                for i in members:
                    new[i] = vector[i] + sum(vector[j] for j in trans[i*args.h:(i+1)*args.h] if j >= 0)
                scale = max(new)
                vector = [v / scale for v in new]
                estimate = scale - 1
            output["exploratory_rho"] = estimate
    except (TimeoutError, MemoryError) as exc:
        output["stop_reason"] = str(exc)
    if mdd is not None:
        output.update(mdd_nodes=len(mdd.level), union_cache=len(mdd.or_cache),
                      resident_mb=round(resident_bytes() / 2**20, 2))
    output["seconds"] = round(time.monotonic() - start, 3)
    print(json.dumps(output, indent=2), flush=True)


if __name__ == "__main__":
    main()
