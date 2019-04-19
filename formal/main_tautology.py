#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 17.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from logic_expressions.parser import *

print("Syntax: not - '!', implication - '->', and - '&', or - '|', equiv - '<->', xor - '^'")
print("Each formula should be in parenthesis except variants when formula is just one variable.")
print("There is no still possibility to use constants in formula.")
print("Variables might be like python identifier ('x', 'lkajf893483', '_new_var_' for example)\n")

while True:
    try:
        tmp = parse(input('F: '))
        print('is tautology:', tmp.check_tautology())
    except Exception as e:
        print(e)
