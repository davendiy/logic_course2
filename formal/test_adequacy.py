#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 19.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

import sys
from logic_expressions import *

# -------------------------------------------test adequacy theorem--------------------------------------------------

file = open('tests/adequacy_theorem_test.txt', 'w', encoding='utf-8')
sys.stdout = file

F = parse('(((A -> B) -> A) -> A)')
print('Theorem (((A -> B) -> A) -> A)')
test_output = adequacy_theorem(F)
for _, message in test_output:
    print(message)

file.close()
