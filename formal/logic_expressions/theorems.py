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


def theorem_L(f: Formula, st_index=0) -> deque:
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


def theorem_deduction(hypothesis: list, f: Formula, output: deque, st_index=0) -> deque:
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
            tmp = theorem_L(f, st_index + i)
            result += tmp
            i += len(tmp) - 1
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
            result.append((f_i2,
                           MESSAGE.format(f_i2, f_i2.print_form(), f'(MP) for {f_i1} and {tmp2} ({tmp2} is above)')))
            result.append((f_i3,
                           MESSAGE.format(f_i3, f_i3.print_form(), f'(MP) for {tmp1} and {f_i2} ({tmp1} is above)')))
        else:
            raise Exception('something wrong')

        i += 1
    return result


def rule_S1(f_g: Formula, g_h: Formula, st_index=0):
    """ Syllogism rule (S1).

    :param f_g: Formula like F -> G
    :param g_h: Formula like G -> H
    :param st_index: first index of addition formula
    :return: Formula F -> H, output for it - deque((formula, message for printing))
    """
    assert len(f_g.sons) > 1 and len(f_g.sons) > 1, f"couldn't use rule S1 to {f_g.print_form()} and {g_h.print_form()}"
    assert f_g.sons[1] == g_h.sons[0], f"couldn't' use rule S1 to {f_g.print_form()} and {g_h.print_form()}"

    f, g = f_g.sons
    h = g_h.sons[1]

    if isinstance(f, Var):     # if f_g is (f -> g) where f is var, f is need to be converted to formula
        f = Formula(PASS, {f}, f)
        f.name = f_g.sons[0].name

    # creates formal output from f_g, g_h, f to h
    f1 = f
    f2 = f_g
    f3 = g_h
    f4 = modus_pones(f1, f2)
    f5 = modus_pones(f4, f3)

    # modify our formal output using deduction theorem
    output = deque([(f1, ''), (f2, ''), (f3, ''), (f4, ''), (f5, '')])
    output = theorem_deduction([f_g, g_h], f, output, st_index)
    return f.implication(h), output


def rule_S2(f_g_h: Formula, g: Formula, st_index=0):
    """ Syllogism rule (S2)

    :param f_g_h: Formula like (F -> (G -> H))
    :param g: Formula
    :param st_index: first index of addition formula
    :return: Formula F -> H, output for it - deque((formula, message for printing))
    """
    assert len(f_g_h.sons) > 1 and len(f_g_h.sons[1].sons) > 1, \
        f"couldn't use rule (S2) to {f_g_h.print_form()} and {g.print_form()}"

    assert f_g_h.sons[1].sons[0] == g, f"couldn't use rule (S2) to {f_g_h.print_form()} and {g.print_form()}"

    f1 = f_g_h.sons[0]         # creates formal output from f_g_h, g, f to h
    f2 = g
    f3 = f_g_h
    f4 = modus_pones(f1, f3)
    f5 = modus_pones(f2, f4)

    # modify our formal output using deduction theorem
    output = deque([(f1, ''), (f2, ''), (f3, ''), (f4, ''), (f5, '')])
    output = theorem_deduction([f_g_h, g], f1, output, st_index)
    return f1.implication(f_g_h.sons[1].sons[1]), output


def theorem_T1(f: Formula, st_index=0):
    output = deque()
    f1 = axiom_A3(f.neg(), f)
    f1.name = NAME.format(st_index)
    output.append((f1, MESSAGE.format(f1, f1.print_form(), f'Axiom A3 for {f} and {f.neg()}')))

    output += theorem_L(f.neg(), st_index=st_index + 1)

    f2 = output[-1][0]       # !F -> !F
    f3, tmp_output = rule_S2(f1, f2, st_index=st_index + len(output))
    output += tmp_output

    tmp = f.neg().neg()
    tmp2 = f.neg()
    f4 = axiom_A1(tmp, tmp2)
    f4.name = NAME.format(st_index + len(output))
    output.append((f4, MESSAGE.format(f4, f4.print_form(), f'Axiom A1 for {tmp} and {tmp2}')))

    f5, tmp_output = rule_S1(f4, f3, st_index=st_index + len(output))
    output += tmp_output
    return output


if __name__ == '__main__':

    # ----------------------------------------test theorem L------------------------------------------------------------
    F = parse('(A -> B)')
    F.name = 'F'
    test_output = theorem_L(F, 1)

    print(f'{F} = {F.print_form()}')
    print(f'Theorem L for {F}')
    for _, message in test_output:
        print(message)

    # -----------------------------------test deduction theorem---------------------------------------------------------
    test_g = parse('(F -> F)')
    test_g.name = 'G'
    print('\n\n')
    print(f'G = {test_g.print_form()}')
    print(f'Deduction theorem for G |- {F} -> {F}')
    test_output = theorem_deduction([], test_g, test_output, 6)
    for _, message in test_output:
        print(message)
    print('\n\n')

    # ------------------------------------------test rule S1 -----------------------------------------------------------
    a_b = parse('(A -> B)')
    b_c = parse('(B -> C)')

    a_b.name = 'H1'
    b_c.name = 'H2'
    print(f'H1: {a_b.print_form()},\nH2: {b_c.print_form()}')
    rez, test_output = rule_S1(a_b, b_c, 1)
    print(f'rule S1 for H1 and H2: {rez}')

    for _, message in test_output:
        print(message)

    # -------------------------------------------test rule S2-----------------------------------------------------------
    print('\n\n')
    a_b_c = parse('(A -> (B -> C))')
    b = parse('B')

    a_b_c.name = 'T1'
    b.name = 'T2'
    print(f'T1: {a_b_c.print_form()},\nT2: {b.print_form()}')
    rez, test_output = rule_S2(a_b_c, b, 0)

    print(f'rule S2 for T1 and T2: {rez}')

    for _, message in test_output:
        print(message)

    # -----------------------------------------test theorem T1----------------------------------------------------------
    print('\n\n')
    F = parse('F')
    print('Theorem !!F -> F:')
    for _, message in theorem_T1(F, 0):
        print(message)
