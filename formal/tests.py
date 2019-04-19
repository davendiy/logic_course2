#!/usr/bin/env python3
# -*-encoding: utf-8-*-

# created: 19.04.2019
# by David Zashkolny
# 2 course, comp math
# Taras Shevchenko National University of Kyiv
# email: davendiy@gmail.com

from logic_expressions import *
import sys

# -------------------------------------------test theorem L-------------------------------------------------------------

file = open('tests/theorem_l_test.txt', 'w', encoding='utf-8')
sys.stdout = file

F = parse('(A -> B)')
F.name = 'F'
test_output = theorem_L(F, 1)

print(f'{F} = {F.print_form()}')
print(f'Theorem L for {F}')
for _, message in test_output:
    print(message)

file.close()

# -----------------------------------test deduction theorem---------------------------------------------------------
file = open('tests/theorem_deduction_test.txt', 'w', encoding='utf-8')
sys.stdout = file

test_g = parse('(F -> F)')
test_g.name = 'G'
print('\n\n')
print(f'G = {test_g.print_form()}')
print(f'Deduction theorem for G |- {F} -> {F} using formal output from theorem_L')
test_output = theorem_deduction([], test_g, test_output, 6)
for _, message in test_output:
    print(message)
print('\n\n')

file.close()

# ------------------------------------------test rule S1 -----------------------------------------------------------
file = open('tests/rule_S1_test.txt', 'w', encoding='utf-8')
sys.stdout = file

a_b = parse('(A -> B)')
b_c = parse('(B -> C)')

a_b.name = 'H1'
b_c.name = 'H2'
print(f'H1: {a_b.print_form()},\nH2: {b_c.print_form()}')
rez, test_output = rule_S1(a_b, b_c, 1)
print(f'rule S1 for H1 and H2: {rez}')

for _, message in test_output:
    print(message)

file.close()

# -------------------------------------------test rule S2-----------------------------------------------------------
file = open('tests/rule_S2_test.txt', 'w', encoding='utf-8')
sys.stdout = file

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

file.close()

# -----------------------------------------test theorem T1----------------------------------------------------------
file = open('tests/theorem_T1_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
print('Theorem !!F -> F:')
for _, message in theorem_T1(F, 0):
    print(message)

file.close()
# -----------------------------------------test theorem T2----------------------------------------------------------
file = open('tests/theorem_T2_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
print('Theorem F -> !!F:')
for _, message in theorem_T2(F, 0):
    print(message)

file.close()
# -----------------------------------------test theorem T3----------------------------------------------------------
file = open('tests/theorem_T3_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
G = parse('G')
print('Theorem !F -> (F -> G):')
for _, message in theorem_T3(F, G, 0):
    print(message)

file.close()

# -----------------------------------------test theorem T4----------------------------------------------------------
file = open('tests/theorem_T4_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
G = parse('G')
print('Theorem (!G -> !F) -> (F -> G):')
for _, message in theorem_T4(F, G, 0):
    print(message)

file.close()
# -----------------------------------------test theorem T5----------------------------------------------------------
file = open('tests/theorem_T5_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
G = parse('G')
print('Theorem (F -> G) -> (!G -> !F):')
for _, message in theorem_T5(F, G, 0):
    print(message)

file.close()
# -----------------------------------------test theorem T6----------------------------------------------------------
file = open('tests/theorem_T6_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
G = parse('G')
print('Theorem F -> (!G -> !(F -> G))')
for _, message in theorem_T6(F, G, 0):
    print(message)

file.close()
# -----------------------------------------test theorem T7----------------------------------------------------------
file = open('tests/theorem_T7_test.txt', 'w', encoding='utf-8')
sys.stdout = file

print('\n\n')
F = parse('F')
G = parse('G')
print('Theorem (F -> G) -> ((!F -> G) -> G)')
for _, message in theorem_T7(F, G, 0):
    print(message)

file.close()
# -------------------------------------------test Kalmar lemma------------------------------------------------------
file = open('tests/Kalmar_lemma_test.txt', 'w', encoding='utf-8')
sys.stdout = file

x1 = Var('x1')
x2 = Var('x2')
X1 = parse('x1')
X2 = parse('x2')

F = parse('(x1 -> (x2 -> x1))')

x1.set_val(0)
x2.set_val(1)

print(f"Vars: {X1}, {X2}, Values: {x1()}, {x2()}, Pow to alpha: {X1.pow_alpha()}, {X2.pow_alpha()}")
print(f'Formula: {F}, Value: {F()}, Pow to alpha: {F.pow_alpha()}\n\n')
print(f'Hypothesis: {X1.pow_alpha()}, {X2.pow_alpha()}')
print(f'Need to find: {F.pow_alpha()}')
test_output = lemma_Kalmar(F, indexation=True)
for _, message in test_output:
    print(message)

file.close()
