#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 18.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from .formulas import *
from .parser import *

__all__ = ['Formula',
           'Var',
           'parse',
           'IMPLICATION',
           'OR',
           'AND',
           'EQUIV',
           'NOT',
           'PASS',
           'XOR',
           'CONNECTIONS',
           'BINARY',
           'UNARY',
           ]
