#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 18.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

""" Axioms and theorems for formal propositional logic
"""


from collections import deque
from .parser import *
from .formulas import *
from itertools import product

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


def theorem_L(f: Formula, st_index=0, indexation=True) -> deque:
    """ For formula f creates formal output of the proof of the L-theorem.

    :param f: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    # -----------------------------------------------formal output------------------------------------------------------
    f0 = axiom_A2(f, f.implication(f), f)
    f1 = axiom_A1(f, f.implication(f))
    f2 = modus_pones(f1, f0)
    f3 = axiom_A1(f, f)
    f4 = modus_pones(f3, f2)

    # ------------------------------------creating sequential names for formulas----------------------------------------
    if indexation:
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


def theorem_deduction(hypothesis: list, f: Formula, output: deque, st_index=0, indexation=True) -> deque:
    """ Creates formal output for Г |- F -> G having formal output [F1, F2... Fn] for
    Г, F |- G, where G = Fn (deduction theorem).

    :param hypothesis: list of formulas-hypothesis
    :param f: last hypothesis (param hypothesis doesn't have this formula)
    :param output: deque((formula, message for printing)) from other function
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    result = deque()
    i = 0            # index of formula name

    # induction
    for f_i, mess in output:
        if f_i.is_axiom or f_i in hypothesis:         # if F_i is axiom or F_i in Г

            # formal output
            f_i1 = axiom_A1(f_i, f)
            if indexation:
                f_i1.name = NAME.format(st_index + i)
            i += 1
            f_next = modus_pones(f_i, f_i1)
            if indexation:
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
            if indexation:
                f_i1.name = NAME.format(st_index + i)
            i += 1

            f_i2 = modus_pones(tmp2, f_i1)           # (F -> (Fr -> Fi)) == (F -> Fs)
            if indexation:
                f_i2.name = NAME.format(st_index + i)
            i += 1

            f_i3 = modus_pones(tmp1, f_i2)
            if indexation:
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


def rule_S1(f_g: Formula, g_h: Formula, st_index=0, indexation=True):
    """ Syllogism rule (S1).

    :param f_g: Formula like F -> G
    :param g_h: Formula like G -> H
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
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
    output = theorem_deduction([f_g, g_h], f, output, st_index, indexation=indexation)
    return f.implication(h), output


def rule_S2(f_g_h: Formula, g: Formula, st_index=0, indexation=True):
    """ Syllogism rule (S2)

    :param f_g_h: Formula like (F -> (G -> H))
    :param g: Formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
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
    output = theorem_deduction([f_g_h, g], f1, output, st_index, indexation=indexation)
    return f1.implication(f_g_h.sons[1].sons[1]), output


def theorem_T1(f: Formula, st_index=0, indexation=True):
    """ Proofing theorem !!F -> F

    :param f: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    output = deque()
    f1 = axiom_A3(f.neg(), f)
    if indexation:
        f1.name = NAME.format(st_index)
    output.append((f1, MESSAGE.format(f1, f1.print_form(), f'Axiom A3 for {f} and {f.neg()}')))

    output += theorem_L(f.neg(), st_index=st_index + 1, indexation=indexation)

    f2 = output[-1][0]       # !F -> !F
    f3, tmp_output = rule_S2(f1, f2, st_index=st_index + len(output))
    output += tmp_output

    tmp = f.neg().neg()
    tmp2 = f.neg()
    f4 = axiom_A1(tmp, tmp2)
    if indexation:
        f4.name = NAME.format(st_index + len(output))
    output.append((f4, MESSAGE.format(f4, f4.print_form(), f'Axiom A1 for {tmp} and {tmp2}')))

    f5, tmp_output = rule_S1(f4, f3, st_index=st_index + len(output), indexation=indexation)
    output += tmp_output
    return output


def theorem_T2(f: Formula, st_index=0, indexation=True):
    """ Proofing theorem !!F -> F

    :param f: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    output = deque()
    f1 = axiom_A3(f, f.neg().neg())
    if indexation:
        f1.name = NAME.format(st_index)
    output.append((f1, MESSAGE.format(f1, f1.print_form(), f'Axiom A3 for {f} and {f.neg().neg()}')))

    output += theorem_T1(f.neg(), st_index=st_index+1, indexation=indexation)

    f2 = output[-1][0]     # !!!F -> !F

    f3 = modus_pones(f2, f1)
    if indexation:
        f3.name = NAME.format(st_index + len(output))
    output.append((f3, MESSAGE.format(f3, f3.print_form(), f'(MP) for {f2} and {f1}')))

    f4 = axiom_A1(f, f.neg().neg().neg())
    if indexation:
        f4.name = NAME.format(st_index + len(output))
    output.append((f4, MESSAGE.format(f4, f4.print_form(), f'Axiom A1 for {f} and {f.neg().neg().neg()}')))

    f5, tmp_output = rule_S1(f4, f3, st_index=st_index + len(output), indexation=indexation)
    output += tmp_output
    return output


def theorem_T3(f: Formula, g: Formula, st_index=0, indexation=True):
    """ Proofing theorem !F -> (G -> F)

    :param f: formula
    :param g: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """

    f1 = f.neg()                # !F
    f2 = f                      # F
    f3 = axiom_A1(f, g.neg())   # F -> (!G -> F)
    f4 = modus_pones(f2, f3)    # !G -> F
    f5 = axiom_A1(f1, g.neg())  # !F -> (!G -> !F)
    f6 = modus_pones(f1, f5)    # !G -> !F
    f7 = axiom_A3(f, g)         # (!G -> !F) -> ((!G -> F) -> G)
    f8 = modus_pones(f6, f7)    # (!B -> A) -> B
    f9 = modus_pones(f4, f8)    # B

    output = deque([(f1, ''), (f2, ''),
                    (f3, ''), (f4, ''),
                    (f5, ''), (f6, ''),
                    (f7, ''), (f8, ''),
                    (f9, '')])

    output = theorem_deduction([f1], f2, output, indexation=False)
    output = theorem_deduction([], f1, output, st_index=st_index, indexation=indexation)
    return output


def theorem_T4(f: Formula, g: Formula, st_index=0, indexation=True):
    """ Proofing theorem (!G -> !F) -> (F -> G)

    :param f: formula
    :param g: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    f1 = axiom_A3(f, g)
    f2 = (g.neg().implication(f.neg()))
    f3 = modus_pones(f2, f1)
    f4 = axiom_A1(f, g.neg())

    f5, tmp_output = rule_S1(f4, f3, indexation=False)

    output = deque([(f1, ''), (f2, ''), (f3, ''), (f4, '')]) + tmp_output
    output = theorem_deduction([], f2, output, st_index=st_index, indexation=indexation)
    return output


def theorem_T5(f: Formula, g: Formula, st_index=0, indexation=True):
    """ Proofing theorem (F -> G) -> (!G -> !F)

    :param f: formula
    :param g: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    f1 = axiom_A3(g.neg(), f.neg())
    f2 = f.implication(g)
    output = deque([(f1, ''), (f2, '')])
    output += theorem_T2(g, indexation=False)

    f3 = output[-1][0]        # G -> !!G

    f4, tmp_output = rule_S1(f2, f3, indexation=False)
    output += tmp_output

    output += theorem_T1(f)
    f5 = output[-1][0]        # !!F -> G

    f6, tmp_output = rule_S1(f5, f4, indexation=False)
    output += tmp_output

    f7 = modus_pones(f6, f1)
    output.append((f7, ''))

    f8 = axiom_A1(g.neg(), f.neg().neg())
    output.append((f8, ''))

    f9, tmp_output = rule_S1(f8, f7, indexation=False)
    output += tmp_output

    output = theorem_deduction([], f2, output, st_index=st_index, indexation=indexation)
    return output


def theorem_T6(f: Formula, g: Formula, st_index=0, indexation=True):
    """ Proofing theorem  F -> (!G -> !(F -> G))

    :param f: formula
    :param g: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    f1 = f
    output = deque([(f1, '')])
    output += theorem_T5(f.implication(g), g, indexation=False)

    f2 = output[-1][0]     # ((F -> G) -> G) -> (!G -> !(F -> G))

    tmp_output = theorem_deduction([f],
                                   f.implication(g),
                                   deque([(f, ''), (f.implication(g), ''), (modus_pones(f, f.implication(g)), '')]),
                                   indexation=False)

    output += tmp_output
    f3 = output[-1][0]     # (F -> G) -> G
    f4 = modus_pones(f3, f2)
    output.append((f4, ''))

    output = theorem_deduction([], f, output, st_index=st_index, indexation=indexation)
    return output


def theorem_T7(f: Formula, g: Formula, st_index=0, indexation=True) -> deque:

    output = deque()
    if isinstance(f, Var):
        f = Formula(PASS, {f}, f)
    f0 = f.implication(g)
    output.append((f0, ''))
    output += theorem_T5(f, g, indexation=False)

    f1 = output[-1][0]    # (F -> G) -> (!G -> !F)
    f2 = axiom_A3(f, g)
    output.append((f2, ''))
    f3, tmp_output = rule_S1(f1, f2, indexation=False)
    output += tmp_output
    f4 = modus_pones(f0, f3)
    output.append((f4, ''))

    output += theorem_T4(g.neg(), f, indexation=False)
    f5 = output[-1][0]          # (!F -> !!G) -> (!G -> F)

    output += _lemma_T7(f, g, indexation=False)
    f6 = output[-1][0]         # (!F -> G) -> (!F -> !!G)

    f7, tmp_output = rule_S1(f6, f5, indexation=False)
    output += tmp_output

    f8, tmp_output = rule_S1(f7, f4, indexation=False)
    output += tmp_output

    return theorem_deduction([], f0, output, st_index=st_index, indexation=indexation)


def _lemma_T7(f: Formula, g: Formula, st_index=0, indexation=True):
    """ Proofing (!F -> G) -> (!F -> !!G)

    :param f: formula
    :param g: formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    f1 = f.neg()
    f2 = f.neg().implication(g)
    f3 = modus_pones(f1, f2)
    tmp_output = theorem_T2(g)
    f4 = tmp_output[-1][0]
    f5 = modus_pones(f3, f4)

    output = deque([(f1, ''), (f2, ''), (f3, '')]) + tmp_output + deque([(f4, ''), (f5, '')])
    output = theorem_deduction([f2], f1, output, indexation=False)
    output = theorem_deduction([], f2, output, st_index=st_index, indexation=indexation)
    return output


def lemma_Kalmar(f: Formula, st_index=0, indexation=True) -> deque:
    """ Kalmar's lemma for f and its variables that already have own values

    :param f: Formula
    :param st_index: first index of addition formula
    :param indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    if f.operations_count == 0:
        tmp = f.pow_alpha()
        if indexation:
            tmp.name = NAME.format(st_index)
        output = deque([(tmp, MESSAGE.format(tmp, tmp.print_form(),
                                             'from hypothesis'))])

    else:
        if f.main_con == NOT:
            if f():
                output = lemma_Kalmar(f.sons[0], st_index=st_index, indexation=indexation)
            else:
                output = lemma_Kalmar(f.sons[0], st_index=st_index, indexation=indexation)
                output += theorem_T2(output[-1][0], st_index=st_index + len(output), indexation=indexation)
        else:
            if not f.sons[0]():
                output = lemma_Kalmar(f.sons[0], st_index=st_index, indexation=indexation)
                g = output[-1][0]
                output += theorem_T3(f.sons[0], f.sons[1], st_index=st_index+len(output), indexation=indexation)
                tmp = output[-1][0]
                res = modus_pones(g, tmp)
                if indexation:
                    res.name = NAME.format(st_index+len(output))
                output.append((res, MESSAGE.format(res, res.print_form(), f'(MP) to {g} and {tmp}')))
            elif f.sons[1]():
                output = lemma_Kalmar(f.sons[1], st_index=st_index, indexation=indexation)
                h = output[-1][0]
                tmp = axiom_A1(h, f.sons[0])
                if indexation:
                    tmp.name = NAME.format(st_index + len(output))
                output.append((tmp, MESSAGE.format(tmp, tmp.print_form(), f'Axiom A1 for {h} and {f.sons[0]}')))
                res = modus_pones(h, tmp)
                if indexation:
                    res.name = NAME.format(st_index + len(output))

                output.append((res, MESSAGE.format(res, res.print_form(), f'(MP) to {h} and {tmp}')))
            else:
                output = lemma_Kalmar(f.sons[0], st_index=st_index, indexation=indexation)
                g = output[-1][0]
                output += lemma_Kalmar(f.sons[1], st_index=st_index, indexation=indexation)
                h = output[-1][0]

                output += theorem_T6(f.sons[0], f.sons[1], st_index=st_index+len(output), indexation=indexation)
                tmp = output[-1][0]
                res = modus_pones(g, tmp)
                res2 = modus_pones(h, res)

                if indexation:
                    res.name = NAME.format(st_index + len(output))
                    res2.name = NAME.format(st_index + len(output) + 1)

                output.append((res, MESSAGE.format(res, res.print_form(), f'(MP) for {g} and {tmp}')))
                output.append((res2, MESSAGE.format(res2, res2.print_form(), f'(MP) for {h} and {res}')))

    return output


def adequacy_theorem(f: Formula, st_index=0, tmp_indexation=True):
    """ Proofing tautology F like a theorem using algorithm from
    adequacy theorem.

    :param f: Formula (tautology)
    :param st_index: first index of addition formula
    :param tmp_indexation: if True then each formula will have a name
    :return: deque((formula, message for printing))
    """
    if not f.check_tautology():
        raise ValueError(f"{f} isn't tautology!")

    # -----------------build the outputs for all the combinations of variables value using Kalmar lemma-----------------
    outputs = {}
    variables = list(f.vars)
    for el in product([True, False], repeat=len(variables)):
        [var.set_val(val) for var, val in zip(variables, el)]
        output_id = ''.join([str(int(var())) for var in variables])
        outputs[output_id] = lemma_Kalmar(f, indexation=False)    # dictionary {sequence of variables values: output}

    # -----------------------------do all the actions without the indexing----------------------------------------------
    while len(variables) > 1:
        last_var = variables.pop()
        for el in product([True, False], repeat=len(variables)):
            [var.set_val(val) for var, val in zip(variables, el)]         # set value for n-1 variables
            output_id = ''.join([str(int(var())) for var in variables])   # sequence of n-1 variables

            last_var.set_val(1)
            tmp_output_id = output_id + str(int(last_var()))

            # use the deduction theorem to build output from n-1 variables
            hypothesis = [Formula(PASS, {var}, var).pow_alpha() for var in variables]
            tmp_output = theorem_deduction(hypothesis, Formula(PASS, {last_var}, last_var).pow_alpha(),
                                           outputs[tmp_output_id], indexation=False)

            last_var.set_val(0)
            tmp_output_id = output_id + str(int(last_var()))

            tmp_output2 = theorem_deduction(hypothesis, Formula(PASS, {last_var}, last_var).pow_alpha(),
                                            outputs[tmp_output_id], indexation=False)

            f1 = tmp_output[-1][0]    # xn -> F
            f2 = tmp_output2[-1][0]   # !xn -> F

            tmp_output3 = theorem_T7(last_var, f, indexation=False)   # (xn -> F) -> ((!xn -> F) -> F)

            f3 = tmp_output3[-1][0]   # (xn -> F) -> ((!xn -> F) -> F)
            f4 = modus_pones(f1, f3)
            f5 = modus_pones(f2, f4)

            output = tmp_output + tmp_output2 + tmp_output3
            output.append((f4, ''))
            output.append((f5, ''))
            outputs[output_id] = output

    # ----------------------------do the last action with indexing (same with above)------------------------------------
    last_var = variables.pop()
    last_var.set_val(1)
    tmp_output_id = str(int(last_var()))
    tmp_output = theorem_deduction([], Formula(PASS, {last_var}, last_var).pow_alpha(),
                                   outputs[tmp_output_id], st_index=st_index, indexation=tmp_indexation)

    last_var.set_val(0)
    tmp_output_id = str(int(last_var()))
    tmp_output2 = theorem_deduction([], Formula(PASS, {last_var}, last_var).pow_alpha(),
                                    outputs[tmp_output_id], st_index=st_index + len(tmp_output), indexation=tmp_indexation)

    f1 = tmp_output[-1][0]
    f2 = tmp_output2[-1][0]

    tmp_output3 = theorem_T7(last_var, f, st_index=st_index + len(tmp_output) + len(tmp_output2), indexation=tmp_indexation)
    output = tmp_output + tmp_output2 + tmp_output3

    f3 = tmp_output3[-1][0]     # (xn -> F) -> ((!xn -> F) -> F)
    f4 = modus_pones(f1, f3)
    if tmp_indexation:
        f4.name = NAME.format(st_index + len(output))
    f5 = modus_pones(f2, f4)
    if tmp_indexation:
        f5.name = NAME.format(st_index + len(output) + 1)

    output.append((f4, MESSAGE.format(f4, f4.print_form(), f'(MP) for {f1} and {f3}')))
    output.append((f5, MESSAGE.format(f5, f5.print_form(), f'(MP) for {f2} and {f4}')))
    return output


if __name__ == '__main__':

    # -----------------------------------------test lemma for theorem T7------------------------------------------------
    print('\n\n')
    F = parse('F')
    G = parse('G')
    print('Theorem (!F -> G) -> (!F -> !!G)')
    for _, message in _lemma_T7(F, G, 0):
        print(message)
