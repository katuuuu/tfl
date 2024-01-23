import os
from domino_solver import create_smt_model
from domino_parser import parse_dominos

def process_tests(test_folder, output_folder):
    for test_file in os.listdir(test_folder):
        if test_file.endswith('.txt'):
            test_path = os.path.join(test_folder, test_file)
            dominos = parse_dominos(test_path)

            model = create_smt_model(dominos)
            result = "Решение найдено:\n" + str(model) if model else "Решение не найдено"

            output_file = os.path.join(output_folder, f'result_{test_file}')
            with open(output_file, 'w') as file:
                file.write(result)
