#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 18.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from collections import deque
from logic_expressions import *

NAME = 'F_{}'
MESSAGE = '{} = {}     basis: {}'

Formula.print_name = True


def axiom_A1(f: Formula, g: Formula) -> Formula:
    """ For formulas f and g creates axiom from schema A1
    """
    tmp = g.implication(f)        # g -> f
    res = f.implication(tmp)      # f -> (g -> f)
    res.is_axiom = True       # that's for checking in the theorems
    return res


def axiom_A2(f: Formula, g: Formula, h: Formula) -> Formula:
    """ For formulas f, g, h creates axiom from schema A2
    """
    f1 = f.implication(g)       # f -> g
    f2 = f.implication(h)       # f -> h
    g1 = g.implication(h)       # g -> h
    g2 = f.implication(g1)      # f -> (g -> h)
    f3 = f1.implication(f2)     # (f -> g) -> (f -> h)
    res = g2.implication(f3)    # (f -> (g -> h)) -> ((f -> g) -> (f -> h))
    res.is_axiom = True       # that's for checking in the theorems
    return res


def axiom_A3(f: Formula, g: Formula) -> Formula:
    """ For formulas f, g creates axiom from schema A3
    """
    f1 = g.neg().implication(f.neg())    # !g -> !f
    f2 = g.neg().implication(f)          # !g -> f
    f3 = f2.implication(g)               # (!g -> f) -> g
    res = f1.implication(f3)             # (!g -> !f) -> ((!g -> f) -> g)
    res.is_axiom = True
    return res


def modus_pones(f: Formula, f_g: Formula) -> Formula:
    """ For formulas f, f_g (f -> g) creates formula g as a result of the rule 'Modus pones'
    (if it is possible).
    """
    assert f == f_g.sons[0], f"coudn't use (MP) for {f.print_form()} and {f_g.print_form()}"
    assert len(f_g.sons) > 1, f"coudn't use (MP) for {f.print_form()} and {f_g.print_form()}"

    # copy uses for different names
    res = f_g.sons[1].copy()  # type: Formula
    res.by_modus_pones = True           # for checking in theorems
    res.from_modus_pones = (f, f_g)     # for checking in theorems
    return res


def theorem_L(f: Formula, st_index: int) -> deque:
    """ For formula f creates formal output of the proof of the L-theorem.

    :param f: formula
    :param st_index: first index of addition formula
    :return: deque((formula, message for printing))
    """
    # -----------------------------------------------formal output------------------------------------------------------
    f0 = axiom_A2(f, f.implication(f), f)
    f1 = axiom_A1(f, f.implication(f))
    f2 = modus_pones(f1, f0)
    f3 = axiom_A1(f, f)
    f4 = modus_pones(f3, f2)

    # ------------------------------------creating sequential names for formulas----------------------------------------
    f0.name = NAME.format(st_index)
    f1.name = NAME.format(st_index + 1)
    f2.name = NAME.format(st_index + 2)
    f3.name = NAME.format(st_index + 3)
    f4.name = NAME.format(st_index + 4)

    # ---------------------------------adding formulas and messages to the deque----------------------------------------
    result = deque()
    result.append((f0, MESSAGE.format(f0, f0.print_form(), f'Axiom A2 for {f}, {f.implication(f)} and {f}')))
    result.append((f1, MESSAGE.format(f1, f1.print_form(), f'Axiom A1 for {f} and {f.implication(f)}')))
    result.append((f2, MESSAGE.format(f2, f2.print_form(), f'(MP) for {f1} and {f0}')))
    result.append((f3, MESSAGE.format(f3, f3.print_form(), f'Axiom A1 for {f} and {f}')))
    result.append((f4, MESSAGE.format(f4, f4.print_form(), f'(MP) for {f3} and {f2}')))
    return result


def theorem_deduction(hypothesis: list, f: Formula, output: deque, st_index: int) -> deque:
    """ Creates formal output for Г |- F -> G having formal output [F1, F2... Fn] for
    Г, F |- G, where G = Fn (deduction theorem).

    :param hypothesis: list of formulas-hypothesis
    :param f: last hypothesis (param hypothesis doesn't have this formula)
    :param output: deque((formula, message for printing)) from other function
    :param st_index: first index of addition formula
    :return: deque((formula, message for printing))
    """
    result = deque()
    i = 0            # index of formula name

    # induction
    for f_i, mess in output:
        if f_i.is_axiom or f_i in hypothesis:         # if F_i is axiom or F_i in Г

            # formal output
            f_i1 = axiom_A1(f_i, f)
            f_i1.name = NAME.format(st_index + i)
            i += 1
            f_next = modus_pones(f_i, f_i1)
            f_next.name = NAME.format(st_index + i)

            # adding to the deque
            result.append((f_i1, MESSAGE.format(f_i1, f_i1.print_form(), f'Axiom A1 for {f_i} and {f}')))
            result.append((f_next, MESSAGE.format(f_next, f_next.print_form(), f'(MP) for {f_i} and  {f_i1}')))

        elif f_i == f:               # if F_i == F then it is enough to proof theorem L
            tmp = theorem_L(f, i)
            result += tmp
        elif f_i.by_modus_pones:     # if F_i was created as a result of any modus pones in the past
            f_pre1, f_pre2 = f_i.from_modus_pones
            tmp1 = f.implication(f_pre1)             # (F -> Fr)
            tmp2 = f.implication(f_pre2)             # (F -> Fs)

            f_i1 = axiom_A2(f, f_pre1, f_i)          # (F -> (Fr -> Fi)) -> ((F -> Fr) -> (F -> Fi))
            f_i1.name = NAME.format(st_index + i)
            i += 1

            f_i2 = modus_pones(tmp2, f_i1)           # (F -> (Fr -> Fi)) == (F -> Fs)
            f_i2.name = NAME.format(st_index + i)
            i += 1

            f_i3 = modus_pones(tmp1, f_i2)
            f_i3.name = NAME.format(st_index + i)

            # adding to the deque
            result.append((f_i1, MESSAGE.format(f_i1, f_i1.print_form(), f'Axiom A2 for {f_pre1} and {f_pre2}')))
            result.append((f_i2, MESSAGE.format(f_i2, f_i2.print_form(), f'(MP) for {f_i1} and {tmp2}')))
            result.append((f_i3, MESSAGE.format(f_i3, f_i3.print_form(), f'(MP) for {tmp1} and {f_i2}')))
        else:
            raise Exception('something wrong')
    return result


if __name__ == '__main__':
    F = parse('(A -> B)')
    F.name = 'F'
    output = theorem_L(F, 1)

    print(f'{F} = {F.print_form()}')
    print(f'Theorem L for {F}')
    for tmp, mess in output:
        print(mess)

    test_g = parse('(F -> F)')
    test_g.name = 'G'
    print('\n\n')
    print(f'G = {test_g.print_form()}')
    print(f'Deduction theorem for G |- {F} -> {F}')
    output = theorem_deduction([], test_g, output, 6)
    for tmp, mess in output:
        print(mess)
