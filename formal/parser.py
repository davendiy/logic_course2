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
binary_regex = re.compile(r'&|->|<->|\^|\|')


class ErrorLogicExpression(Exception):

    def __str__(self):
        return 'Bad logic expression'


def sequence(*funcs):
    """ Sequence of functions-generators (from https://habr.com/ru/post/309242/)

    :param funcs: callable
    :return: callable for parsing
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


def parse_ident(src):
    """ Parse the first identifier

    :param src: string
    :return: first identifier, other string
    """
    match = ident_regex.match(src)
    if match is not None:
        val = match.group()
        yield val, src[len(val):].lstrip()


def parse_binary(src):
    """ Parse the binary operation

    :param src: string
    :return: first binary operation, other string
    """
    match = binary_regex.match(src)
    if match is not None:
        val = match.group()
        yield val, src[len(val):].lstrip()


def parse_word(word, value=None):
    """ Create the function that parses the given word

    :param word: string
    :param value: default value that will returns the function
    :return: callable
    """
    start = len(word)

    def result(src: str):
        if src.startswith(word):
            yield value, src[start:].lstrip()

    result.__name__ = f"parse_{word}"
    return result


# addintion parsers
parse_not = parse_word('!', NOT)
parse_left_par = parse_word('(', LEFT_PAR)
parse_right_par = parse_word(')', RIGHT_PAR)
parse_empty_array = sequence(parse_left_par, parse_right_par)


def parse_formula(src):
    """ Parse the first formula in logic utterances.

    :param src: string
    :return: Formula, other string
    """

    # try to parse the variant, when formula is just one variable
    for var, src in parse_ident(src):
        tmp = Var(var)
        yield Formula(PASS, {tmp, }, tmp), src   # return for stop the iterator
        return

    # try to parse the variant when formula is like (A * B), * - binary operation
    for (_, form1, oper, form2, _), src in sequence(parse_left_par,
                                                    parse_formula,
                                                    parse_binary,
                                                    parse_formula,
                                                    parse_right_par)(src):
        yield form1._binary(form2, operation_type=oper), src
        return

    # try to parse the variant when formula is like (*A), * - unary operation (still just not)
    for (_, _, form, _), src in sequence(parse_left_par,
                                         parse_not,
                                         parse_formula,
                                         parse_right_par)(src):
        yield form.neg(), src
        return

    # try to parse the variant when formula is like (A)
    for (_, form, _), src in sequence(parse_left_par,
                                      parse_formula,
                                      parse_right_par)(src):
        yield form.neg(), src
        return

    # if there was no variant that satisfies src returns None (bad logic expression)


def parse(s) -> Formula:
    """ Parse the formula using the function from above.

    :param s: string
    :return: Formula
    """
    s = s.strip()
    match = list(parse_formula(s))
    if len(match) != 1:          # if we haven't found formula or any other symbols have left
        raise ErrorLogicExpression   # it means that given expresiion is bad
    result, src = match[0]
    if src.strip():
        raise ErrorLogicExpression
    return result


if __name__ == '__main__':
    print(parse('(((!x1) -> (x2 | (!x3))) <-> (x1 & x2))'))

    print(parse('x1'))

    F = parse('(A -> (!(!A)))')
    print('F = ', F)
    print('=|F:', F.check_tautology())
