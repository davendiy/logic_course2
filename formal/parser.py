#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 17.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from formulas import *
import re


ident_regex = re.compile(r'[_a-zA-Z][_a-zA-Z0-9]*')


def sequence(*funcs):
    """ Sequence of functions-generators (from https://habr.com/ru/post/309242/)

    :param funcs: callable
    :return:
    """
    if len(funcs) == 0:
        def result(src):
            yield (), src
        return result

    def result(src):
        for arg1, src in funcs[0](src):
            for others, src in sequence(*funcs[1:])(src):
                yield (arg1,) + others, src
    return result


class ErrorLogicExpression(Exception):

    def __str__(self):
        return 'Bad logic expression'


def parse_regex(src):
    match = ident_regex.match(src)
    if match is not None:
        val = match.group()
        yield val, src[len(val):].lstrip()


def parse_word(word, value=None):
    start = len(word)

    def result(src: str):
        if src.startswith(word):
            yield value, src[start:].lstrip()

    result.__name__ = f"parse_{word}"
    return result


# parse_true = parse_word('1', True)
# parse_false = parse_word('0', False)
parse_implication = parse_word('->', IMPLICATION)
parse_not = parse_word('!', NOT)
parse_left_par = parse_word('(', LEFT_PAR)
parse_right_par = parse_word(')', RIGHT_PAR)
parse_empty_array = sequence(parse_left_par, parse_right_par)


def parse_formula(src):

    for var, src in parse_regex(src):
        tmp = Var(var)
        yield Formula(PASS, {tmp, }, tmp), src
        return

    for (_, form1, _, form2, _), src in sequence(parse_left_par,
                                                 parse_formula,
                                                 parse_implication,
                                                 parse_formula,
                                                 parse_right_par)(src):
        yield form1.implication(form2), src
        return

    for (_, _, form, _), src in sequence(parse_left_par,
                                         parse_not,
                                         parse_formula,
                                         parse_right_par)(src):
        yield form.neg(), src
        return


def parse(s) -> Formula:
    s = s.strip()
    match = list(parse_formula(s))
    if len(match) != 1:
        raise ErrorLogicExpression
    result, src = match[0]
    if src.strip():
        raise ErrorLogicExpression
    return result


if __name__ == '__main__':
    print(parse('((!x1) -> (x2 -> (!x3)))'))

    print(parse('x1'))

    tmp = parse('(A -> (!(!A)))')
    print('F = ', tmp)
    print('=|F:', tmp.check_tautology())
