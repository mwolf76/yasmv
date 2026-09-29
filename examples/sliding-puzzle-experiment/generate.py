#!/usr/bin/env python3
"""Generate the opposite-parity square sliding puzzle, with no parity lemma."""
import argparse
from pathlib import Path

DIRECTIONS = ((-1, 0, 'UP'), (0, 1, 'RIGHT'), (1, 0, 'DOWN'), (0, -1, 'LEFT'))


def boards(side):
    initial = list(range(1, side * side)) + [0]
    goal = initial.copy()
    goal[-3], goal[-2] = goal[-2], goal[-3]
    return initial, goal


def neighbors(side, position):
    row, column = divmod(position, side)
    return [(side * (row + dr) + column + dc, move) for dr, dc, move in DIRECTIONS
            if 0 <= row + dr < side and 0 <= column + dc < side]


def source(side):
    if side < 2 or side > 16 or side & (side - 1):
        raise ValueError('Side must be one of 2, 4, 8, 16')
    count, width = side * side, (side * side - 1).bit_length()
    initial, goal = boards(side)
    lines = [f'-- {count-1}-puzzle: {side} by {side}; swap the last two numbered tiles.',
             '-- Source: Johnson and Story, Notes on the 15 Puzzle, 1879.',
             '-- Guarded adjacent swaps on scalar cells. No parity lemma.',
             f'#word-width {width}', 'MODULE main']
    for i in range(count):
        lines.extend(['#inertial', f'VAR cell_{i} : uint{width};'])
    lines.append('VAR move : { UP, RIGHT, DOWN, LEFT };')
    for i, value in enumerate(initial): lines.append(f'INIT cell_{i} = {value};')
    lines.append('DEFINE GOAL := ' + ' && '.join(f'cell_{i} = {value}' for i,value in enumerate(goal)) + ';')
    lines.append('-- Well-formed boards: the fixed-width labels form a permutation.')
    for a in range(count):
        for b in range(a + 1, count):
            lines.append(f'INVAR cell_{a} != cell_{b};')
    lines.append('-- Exactly one legal adjacent slide per transition; no idle move.')
    for position in range(count):
        options = ' || '.join('move = ' + direction for _, direction in neighbors(side, position))
        lines.append(f'INVAR cell_{position} = 0 -> ({options});')
    for position in range(count):
        for adjacent, direction in neighbors(side, position):
            lines.append(f'TRANS cell_{position} = 0 && cell_{adjacent} != 0 && move = {direction} ?:'
                         f' cell_{position} := cell_{adjacent}, cell_{adjacent} := 0;')
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--side', type=int, default=8)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(source(args.side))
