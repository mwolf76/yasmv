#!/usr/bin/env python3
"""Independent puzzle oracle, exhaustive small encoding checks, and all-k witness."""
from collections import deque
import itertools
import json
from pathlib import Path
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path[:0] = [str(HERE), str(ROOT)]
from generate import boards, source
from tools.workbench.sessions import Session


def slide(board, side, direction):
    blank = board.index(0)
    row, col = divmod(blank, side)
    dr, dc = {'UP':(-1,0), 'DOWN':(1,0), 'LEFT':(0,-1), 'RIGHT':(0,1)}[direction]
    nr, nc = row+dr, col+dc
    if not (0 <= nr < side and 0 <= nc < side): return None
    dest = nr*side+nc
    result = list(board); result[blank], result[dest] = result[dest], result[blank]
    return tuple(result)


def parity(board, side):
    # Include the blank as label 0; a slide toggles both terms.
    permutation = sum(a > b for i,a in enumerate(board) for b in board[i+1:]) % 2
    row, col = divmod(board.index(0), side)
    return permutation ^ ((row+col) % 2)


def all_k_witness(side, k):
    goal = tuple(boards(side)[1])
    a = slide(goal, side, 'LEFT')
    b = slide(a, side, 'UP')
    # End in A then RIGHT to G. Alternate A/B for any requested prefix length.
    prefix = [a if (k-1-i)%2==0 else b for i in range(k)]
    return prefix+[goal]


def main():
    initial, goal = map(tuple, boards(2))
    reached={initial}; queue=deque([initial])
    while queue:
        board=queue.popleft()
        for direction in ('UP','DOWN','LEFT','RIGHT'):
            successor=slide(board,2,direction)
            if successor is not None:
                assert parity(board,2)==parity(successor,2)
                if successor not in reached: reached.add(successor); queue.append(successor)
    assert len(reached)==12 and goal not in reached
    generic='\n'.join(line for line in source(2).splitlines() if not line.startswith('INIT '))+'\n'
    session=Session(str(ROOT/'yasmv'),str(ROOT),dict(source=generic,root='',inputs={}),threading.Event(),time.monotonic()+120)
    checked=0
    def query(value):
        result=session.query(dict(value,request_id='oracle'),threading.Event(),time.monotonic()+30)
        assert result['status']=='completed',result
        return result
    try:
        for board in itertools.permutations(range(4)):
            for direction in ('UP','DOWN','LEFT','RIGHT'):
                condition=' && '.join(f'cell_{i} = {v}' for i,v in enumerate(board))+' && move = '+direction
                picked=query(dict(operation='pick-state',assumptions=[condition]))
                successor=slide(board,2,direction)
                if successor is None:
                    assert picked['outcome']=='unsatisfiable',picked
                else:
                    assert picked['trace'],picked
                    advanced=query(dict(operation='simulate',trace=picked['trace'],limits=dict(depth=1)))
                    assert advanced['outcome']=='simulated',advanced
                    observed=tuple(int(advanced['trace']['steps'][-1]['values'][f'cell_{i}']) for i in range(4))
                    assert observed==successor,(board,direction,observed,successor)
                    checked+=1
    finally: session.close()
    initial, goal = map(tuple, boards(8))
    assert parity(initial,8)!=parity(goal,8)
    for k in (1,2,3,4,8,16,63,64,127,1024):
        path=all_k_witness(8,k)
        assert path[-1]==goal and all(s!=goal for s in path[:-1])
        assert all(sorted(s)==list(range(64)) for s in path)
        for a,b in zip(path,path[1:]):
            assert b in [slide(a,8,d) for d in ('UP','DOWN','LEFT','RIGHT')]
    assert (HERE/'puzzle-63.smv').read_text()==source(8)
    print('PASS: 24 small boards, 96 action checks, 48 exact legal successors; BFS component has 12 boards.')
    print('PASS: 63-puzzle generation and parity; constructive induction-step witnesses through k=1024.')
    session=Session(str(ROOT/'yasmv'),str(ROOT),dict(source=source(2),root='',inputs={}),threading.Event(),time.monotonic()+60)
    try:
        result=query(dict(operation='reach',strategy='interpolation',target='GOAL',limits=dict(wall_ms=30000)))
        assert result['outcome']=='unreachable' and result['proof']['verified'] and not result['proof']['vacuous'],result
        output=HERE/'results'; output.mkdir(exist_ok=True)
        (output/'small-control.json').write_text(json.dumps(result,indent=2)+'\n')
        print('PASS: interpolation proves the same puzzle on 2x2, with fresh invariant verification.')
    finally: session.close()


if __name__ == '__main__': main()
