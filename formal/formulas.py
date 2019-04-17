#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 17.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from itertools import product

IMPLICATION = ' -> '
NOT = '!'
PASS = ''

LEFT_PAR = '('
RIGHT_PAR = ')'

CONNECTIONS = [IMPLICATION, NOT, PASS]
BINARY = [IMPLICATION, ]
UNARY = [NOT, PASS]


FUNCTIONS = {IMPLICATION: lambda a, b: not a or b,
             NOT: lambda a: not a,
             PASS: lambda a: a,
             }


class Var:
    """ Variable in logic of utterances.

    Might to be True or False (1 or 0 respectively)
    """

    _vars = {}

    def __new__(cls, name):
        if name not in Var._vars:
            Var._vars[name] = object.__new__(cls)

        return Var._vars[name]

    def __init__(self, name: str):
        assert name.isidentifier()
        self.name = name
        self._val = 0

    def set_val(self, value):
        assert value in [0, 1] or value in [True, False], 'bad value for variable'
        self._val = bool(value)

    def __call__(self, *args, **kwargs):
        return self._val

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return self.name

    def __repr__(self):
        return f'Var({self.name})'


class Formula:

    def __init__(self, main_con, variables:set, *sons):
        assert main_con in CONNECTIONS, 'bad connection'
        assert all(isinstance(var, Var) for var in variables)

        self.main_con = main_con
        self.sons = sons
        self.vars = variables
        self._is_tautology = None

    def neg(self):
        return Formula(NOT, self.vars, self)

    def implication(self, other):
        assert isinstance(other, Formula) or isinstance(other, Var), 'bad component'

        if isinstance(other, Formula):
            return Formula(IMPLICATION, self.vars | other.vars, self, other)
        else:
            return Formula(IMPLICATION, self.vars | {other}, self, other)

    def check_tautology(self):
        if self._is_tautology is None:
            success = True
            for el in product([True, False], repeat=len(self.vars)):
                tmp = list(self.vars)
                for var, val in zip(tmp, el):
                    var.set_val(val)
                if not self.__call__():
                    success = False
                    break
            self._is_tautology = success
        return self._is_tautology

    def __call__(self, *args, **kwargs):
        return FUNCTIONS[self.main_con](*[el() for el in self.sons])

    def __str__(self):
        if self.main_con in BINARY:
            return LEFT_PAR + str(self.sons[0]) + self.main_con + str(self.sons[1]) + RIGHT_PAR
        elif self.main_con != PASS:
            return LEFT_PAR + self.main_con + str(self.sons[0]) + RIGHT_PAR
        else:
            return str(self.sons[0])

    def __repr__(self):
        return f'Formula({self.main_con}, {self.vars}, {self.sons})'


if __name__ == '__main__':
    x1 = Var('x1')
    x2 = Var('x2')

    F1 = Formula(PASS, {x1}, x1)
    F1 = F1.neg()
    F2 = F1.implication(x2)

    F3 = F2.implication(F1)

    print("F3 =", F3)

    x1.set_val(1)
    x2.set_val(0)
    print('F3(1, 0) =', F3())

    print('\n\n')
    F1 = Formula(PASS, {x1}, x1)
    F2 = Formula(PASS, {x2}, x2)

    F3 = F1.implication(F2.implication(F1))
    print(F3)
    print('=|F3 -', F3.check_tautology())
