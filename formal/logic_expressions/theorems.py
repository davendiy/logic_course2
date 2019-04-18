#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 18.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from collections import deque
from logic_expressions import *


def axiom_A1(f: Formula, g: Formula):
    tmp = g.implication(f)        # g -> f
    return f.implication(tmp)     # f -> (g -> f)


def axiom_A2(f: Formula, g: Formula, h: Formula):
    f1 = f.implication(g)       # f -> g
    f2 = f.implication(h)       # f -> h
    g1 = g.implication(h)       # g -> h
    g2 = f.implication(g1)      # f -> (g -> h)
    f3 = f1.implication(f2)     # (f -> g) -> (f -> h)
    return g2.implication(f3)   # (f -> (g -> h)) -> ((f -> g) -> (f -> h))


def axiom_A3(f: Formula, g: Formula):
    f1 = g.neg().implication(f.neg())    # !g -> !f
    f2 = g.neg().implication(f)          # !g -> f
    f3 = f2.implication(g)               # (!g -> f) -> g
    return f1.implication(f3)            # (!g -> !f) -> ((!g -> f) -> g)


def modus_pones(f: Formula, f_g: Formula):
    assert f == f_g.sons[0], f"coudn't use (MP) for {f} and {f_g}"
    assert len(f_g.sons) > 1, f"coudn't use (MP) for {f} and {f_g}"

    return f_g.sons[1]


def theorem_L(f: Formula, start_index: int) -> deque:
    f0 = axiom_A2(f, f.implication(f), f)
    f1 = axiom_A1(f, f.implication(f))
    f2 = modus_pones(f1, f0)
    f3 = axiom_A1(f, f)
    f4 = modus_pones(f3, f2)

    message = 'F{} = {}     basis: {}'

    result = deque()
    result.appendleft((f0, message.format(start_index, f0, f'Axiom A2 for {f}, {f.implication(f)} and {f}')))
    result.appendleft((f1, message.format(start_index + 1, f1, f'Axiom A1 for {f} and {f.implication(f)}')))
    result.appendleft((f2, message.format(start_index + 2, f2, f'(MP) for F{start_index + 1} and F{start_index}')))
    result.appendleft((f3, message.format(start_index + 3, f3, f'Axiom A1 for {f} and {f}')))
    result.appendleft((f4, message.format(start_index + 4, f4, f'(MP) for F{start_index + 3} and F{start_index + 2}')))
    return result


if __name__ == '__main__':
    F = parse('((A -> B) -> C)')

    output = theorem_L(F, 1)
    while output:
        tmp, mess = output.pop()
        print(mess)
