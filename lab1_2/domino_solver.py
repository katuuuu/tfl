from z3 import *
from math import *

def generate_equations(dominos, M, N):
    equations = []
    letter_counts = {}

    for i, (left, right) in enumerate(dominos):
        for letter in set(left + right):
            if letter not in letter_counts:
                letter_counts[letter] = 0
            letter_counts[letter] += M[i] * (left.count(letter) - right.count(letter))

    # Уравнение для каждой буквы
    for letter, count in letter_counts.items():
        equations.append(count == 0)


    for i in range(len(dominos)):
        for j in range(len(dominos)):
            if dominos[i][1] == dominos[j][0]:
                equations.append(N[i][j] <= M[i])
                equations.append(N[i][j] <= M[j])

    # Краевое домино
    # Ni,j для первого и последнего домино равна 1
    equations.append(Sum([N[0][j] for j in range(len(dominos))]) == 1)
    equations.append(Sum([N[i][len(dominos) - 1] for i in range(len(dominos))]) == 1)

    return equations

def create_smt_model(dominos):
    s = Solver()
    M = [Int(f'M{i}') for i in range(len(dominos))]
    for mi in M:
        s.add(mi > 0)

    N = [[Int(f'N{i}{j}') for j in range(len(dominos))] for i in range(len(dominos))]
    for i in range(len(dominos)):
        for j in range(len(dominos)):
            s.add(N[i][j] >= 0, N[i][j] <= M[i], N[i][j] <= M[j])

    equations = generate_equations(dominos, M, N)
    for eq in equations:
        s.add(eq)

    if s.check() == sat:
        return s.model()
    else:
        return None

