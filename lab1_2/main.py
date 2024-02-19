from domino_alg import read_domino_pairs_from_file, initialize_counts, analyze_domino_pairs
def main(file_path,output_file_path):
    # Извлекаем последнюю строку и удаляем символы перевода строки
    with open(file_path, 'r') as file:
        lines = file.readlines()
        solution_string = lines[len(lines) - 1]
    domino_pairs = read_domino_pairs_from_file(file_path)
    domino_count, neighbor_count = initialize_counts(domino_pairs)

    analyze_domino_pairs(domino_pairs, domino_count, neighbor_count, solution_string, output_file_path)

if __name__ == '__main__':
    for i in range(1, 11):
        file_path = 'test\\test' + str(i) + '.txt'
        output_file_path = 'test\\result\\result' + str(i) + '.txt'
        main(file_path, output_file_path)

