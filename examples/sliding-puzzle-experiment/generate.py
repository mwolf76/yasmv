#!/usr/bin/env python3
"""Generate an opposite-parity rectangular sliding puzzle, with no parity lemma."""
import argparse
from pathlib import Path

DIRECTIONS = ((-1, 0, 'UP'), (0, 1, 'RIGHT'), (1, 0, 'DOWN'), (0, -1, 'LEFT'))


def boards(rows, columns=None):
    columns = rows if columns is None else columns
    initial = list(range(1, rows * columns)) + [0]
    goal = initial.copy()
    goal[-3], goal[-2] = goal[-2], goal[-3]
    return initial, goal


def neighbors(rows, position, columns=None):
    columns = rows if columns is None else columns
    row, column = divmod(position, columns)
    return [(columns * (row + dr) + column + dc, move) for dr, dc, move in DIRECTIONS
            if 0 <= row + dr < rows and 0 <= column + dc < columns]


def source(rows, columns=None):
    columns = rows if columns is None else columns
    if any(d not in (2, 4, 8, 16) for d in (rows, columns)):
        raise ValueError('Each dimension must be one of 2, 4, 8, 16')
    count, width = rows * columns, (rows * columns - 1).bit_length()
    initial, goal = boards(rows, columns)
    lines = [f'-- {count-1}-puzzle: {rows} by {columns}; swap the last two numbered tiles.',
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
        options = ' || '.join('move = ' + direction for _, direction in neighbors(rows, position, columns))
        lines.append(f'INVAR cell_{position} = 0 -> ({options});')
    for position in range(count):
        for adjacent, direction in neighbors(rows, position, columns):
            lines.append(f'TRANS cell_{position} = 0 && cell_{adjacent} != 0 && move = {direction} ?:'
                         f' cell_{position} := cell_{adjacent}, cell_{adjacent} := 0;')
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    dimensions = parser.add_mutually_exclusive_group()
    dimensions.add_argument('--side', type=int, help='Square board size (default: 8)')
    dimensions.add_argument('--rows', type=int, help='Rectangular board height; requires --columns')
    parser.add_argument('--columns', type=int, help='Rectangular board width; requires --rows')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if (args.rows is None) != (args.columns is None):
        parser.error('--rows and --columns must be specified together')
    try:
        model = source(args.rows, args.columns) if args.rows is not None else source(8 if args.side is None else args.side)
    except ValueError as error:
        parser.error(str(error))
    args.output.write_text(model)
