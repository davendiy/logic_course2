#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 19.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from logic_expressions import *

with open('output.txt', 'w', encoding='utf-8') as file:

    print("Please, enter the tautology using any names for variables, '->' for implication and '!' for NOT")
    f = parse(input('--> '))
    test_output = adequacy_theorem(f)
    file.write(f'last formula: {test_output[-1][1]}\n\n\n')
    for _, message in test_output:
        file.write(message + '\n')
