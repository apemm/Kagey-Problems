"""Extract a certified internal greedy bridge from a completed sea graph."""
from pathlib import Path
import argparse
import json
import struct
import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('height', type=int)
    parser.add_argument('word')
    args = parser.parse_args()
    h = args.height
    word = tuple(map(int, args.word.split(',')))
    graph = HERE / f'sea_packed_h{h}.bin'
    report = json.loads((HERE / f'sea_packed_h{h}.json').read_text())
    with graph.open('rb') as source:
        magic, height, n = struct.unpack('<iii', source.read(12))
    assert magic == 0x53454731 and height == h
    edges = np.memmap(graph, mode='r', dtype='<i4', offset=12, shape=(n,h))
    components = np.memmap(str(graph)+'.components', mode='r', dtype='<i4', offset=4, shape=(n,))
    history_length = 2*(1+(h-1)**2//4)
    prefix = word * ((history_length+len(word)-1)//len(word)+1)
    state = 0
    for row in prefix:
        state = int(edges[state,row-1])
        assert state >= 0
    start_state = state
    cid = int(components[state])
    target = report['components']['constant_states'][0]
    assert int(components[target]) == cid
    bridge = []
    seen = set()
    while state != target:
        assert state not in seen
        seen.add(state)
        for row, successor in enumerate(edges[state],1):
            if successor >= 0 and int(components[successor]) == cid:
                state = int(successor)
                bridge.append(row)
                break
        else:
            raise AssertionError('No internal successor')
    result = dict(height=h, periodic_past=word, prefix_length=len(prefix),
                  start_state=start_state, component=cid,
                  bridge=bridge, bridge_length=len(bridge),
                  target_constant_row=1, target_state=target)
    path = HERE / ('periodic_bridge_h'+str(h)+'_'+args.word.replace(',','_')+'.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
