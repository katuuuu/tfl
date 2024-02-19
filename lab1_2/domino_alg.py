from z3 import *


# Функция для чтения пар домино из файла
def read_domino_pairs_from_file(file_path):
    domino_pairs = []
    with open(file_path, 'r') as f:
        for line in f:
            pair = line.strip().split(',')
            if len(pair) == 2:  # Проверяем, что строка содержит две части
                domino_pairs.append([pair[0], pair[1]])
    return domino_pairs

# Функция инициализации счетчиков для каждого домино и пар соседних домино
def initialize_counts(domino_pairs):
    domino_count = {i: Int('domino_count_{}'.format(i)) for i in range(len(domino_pairs))}
    neighbor_count = {(i, j): Int('neighbor_count_{}_{}'.format(i, j)) for i in range(len(domino_pairs)) for j in range(len(domino_pairs)) if i != j}
    return domino_count, neighbor_count

# Функция анализа пар домино
def analyze_domino_pairs(domino_pairs, domino_count, neighbor_count, solution_string, output_file_path):
    s = Solver()

    # Уравнения на число вхождений каждого домино
    for i in range(len(domino_pairs)):
        s.add(domino_count[i] == solution_string.count(domino_pairs[i][0] + domino_pairs[i][1]))

    # Уравнения на число соседств между домино
    for i in range(len(domino_pairs)):
        for j in range(i + 1, len(domino_pairs)):
            neighbor_count_value = solution_string.count(
                domino_pairs[i][0] + domino_pairs[j][1]) + solution_string.count(
                domino_pairs[i][1] + domino_pairs[j][0])
            s.add(neighbor_count[(i, j)] == If(neighbor_count_value > 1, neighbor_count_value, 0))
            s.add(neighbor_count[(j, i)] == neighbor_count[(i, j)])

    # Проверка на неудовлетворимость
    if not s.check():
        print("Соответствие Поста не разрешимо")
        return

    if s.check() == z3.sat:
        model = s.model()

        # Вывод числа вхождений каждого домино
        with open(output_file_path, 'w') as f:
            f.write("Число вхождений каждого домино:\n")
            for i in range(len(domino_pairs)):
                f.write("{}: {}\n".format(domino_pairs[i], model[domino_count[i]].as_long()))

        # Вывод числа соседств между домино
        with open(output_file_path, 'a') as f:
            f.write("\nЧисло соседств между домино:\n")
            for i in range(len(domino_pairs)):
                for j in range(i + 1, len(domino_pairs)):
                    neighbor_count_value = model[neighbor_count[(i, j)]].as_long()
                    f.write("{} и {}: {}\n".format(domino_pairs[i], domino_pairs[j], neighbor_count_value))
    else:
        print("Соответствие Поста не разрешимо")
        return