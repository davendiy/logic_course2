#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 17.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from itertools import product

# Global constants for operations
IMPLICATION = '->'
NOT = '!'
PASS = ''
OR = '|'
AND = '&'
XOR = '^'
EQUIV = '<->'

# parenthesis
LEFT_PAR = '('
RIGHT_PAR = ')'

BINARY = (IMPLICATION, OR, AND, XOR, EQUIV)   # all the binary operations
UNARY = (NOT, PASS)                           # all the unary operations
CONNECTIONS = BINARY + UNARY

# dictionary with the functions for each operation
FUNCTIONS = {OR: lambda a, b: a or b,
             AND: lambda a, b: a and b,
             EQUIV: lambda a, b: (a and b) or (not a and not b),
             XOR: lambda a, b: not((a and b) or (not a and not b)),
             IMPLICATION: lambda a, b: not a or b,
             NOT: lambda a: not a,
             PASS: lambda a: a,
             }


class Var:
    """ Variable in logic of utterances.

    Might to be True or False (1 or 0 respectively)
    """

    _vars = {}

    def __new__(cls, name):
        """ This is because of we need to have only one representative for each variable.

        # For example
        >>> x1 = Var('x1')
        >>> x2 = Var('x1')
        >>> x1 == x2
        True
        >>> x1 is x2      # it means that x1 and x2 are hrefs on the one object
        True

        :param name: name of variable
        :return: object
        """
        if name not in Var._vars:
            Var._vars[name] = object.__new__(cls)

        return Var._vars[name]

    def __init__(self, name: str):
        assert name.isidentifier()     # check name
        self.name = name
        self._val = 0

    def set_val(self, value):
        assert value in (0, 1, True, False), 'bad value for variable'
        self._val = bool(value)

    def __call__(self, *args, **kwargs):
        return self._val

    def __hash__(self):          # this is for possibility to use the set of Vars
        return hash(self.name)

    def __str__(self):
        return self.name

    def __repr__(self):
        return f'Var({self.name})'


class Formula:
    """ Formula in logic of utterances

    Defines recursively just like math definition.
    """
    def __init__(self, main_con, variables: set, *sons):
        """ Create the formula in logic of utterances with the given main connectivity,
        that have given variables and subformulas

        >>> x1 = Var('x1')
        >>> x2 = Var('x2')
        >>> F1 = Formula(IMPLICATION, {x1, x2}, x1, x2)
        >>> F2 = F1.con(x2)
        >>> F2
        ((x1 -> x2) & x2)

        :param main_con: main connectivity (binary or unary)
        :param variables: set of Vars
        :param sons: subformulas that are connected by main_con
        """
        assert main_con in CONNECTIONS, 'bad connection'
        assert all(isinstance(var, Var) for var in variables)

        self.main_con = main_con
        self.sons = sons
        self.vars = variables
        self._is_tautology = None

    def neg(self):
        """ !self

        :return: Formula
        """
        return Formula(NOT, self.vars, self)

    def _binary(self, other, operation_type):
        """ Binary operation between 2 formulas

        :param other: other formula or variable
        :param operation_type: operations from BINARY
        :return: Formula
        """
        assert isinstance(other, Formula) or isinstance(other, Var), 'bad component'

        if isinstance(other, Formula):
            return Formula(operation_type, self.vars | other.vars, self, other)
        else:
            return Formula(operation_type, self.vars | {other}, self, other)

    def implication(self, other):
        """ self -> other
        """
        return self._binary(other, IMPLICATION)

    def xor(self, other):
        """ self XOR other
        """
        return self._binary(other, XOR)

    def con(self, other):
        """ self AND other
        """
        return self._binary(other, AND)

    def dis(self, other):
        """ self OR other
        """
        return self._binary(other, OR)

    def equiv(self, other):
        """ self <-> other
        """
        return self._binary(other, EQUIV)

    def check_tautology(self):
        """ Check if this formula is tautology using full permute.

        :return: bool
        """
        if self._is_tautology is None:      # if we haven't already check
            success = True
            for el in product([True, False], repeat=len(self.vars)):
                tmp = list(self.vars)
                for var, val in zip(tmp, el):    # set value for each variable
                    var.set_val(val)
                if not self.__call__():        # compute value of formula
                    success = False
                    break
            self._is_tautology = success
        return self._is_tautology

    def __eq__(self, other):
        success = True
        if isinstance(other, Var):
            other = Formula(PASS, {other, }, other)

        if len(self.sons) != len(other.sons) or self.main_con != other.main_con:
            success = False

        for el1, el2 in zip(self.sons, other.sons):
            if el1 != el2:
                success = False
                break
        return success

    def __call__(self, *args, **kwargs):
        """ Recursively compute value of formula.

        Before it calls you need to set values to all the variables (by default they equal 0)
        """
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

    F1 = Formula(IMPLICATION, {x1, x2}, x1, x2)
    F2 = F1.con(x2)
    print('\n\n', F2)
