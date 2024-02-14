import os
from l_table_algorithm import LTableAlgorithm
from parse import read_input
from utils import print_automata
from type import Automata, ParsingError
import config

def process_file(input_path: str, output_path: str):
    try:
        input_data = read_input(input_path)
        oracle = lambda word: input_data.regex.match(word) is not None
        l_table_algorithm = LTableAlgorithm(input_data.alphabet, oracle, config.P, input_data.maxLength)
        automata = l_table_algorithm.compute()
        print_results(automata, output_path)
    except ParsingError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"Unhandled exception: {e}")
        raise e

def print_results(automata: Automata, output_path: str):
    try:
        automata_str = print_automata(automata)
        with open(output_path, 'w') as file:
            file.write(automata_str)
        print(f"Результаты успешно записаны в файл {output_path}.")
    except Exception as e:
        print(f"Ошибка при записи в файл: {e}")

def main():
    input_path = 'input.txt' 
    output_directory = 'output'
    if not os.path.exists(output_directory):
        os.makedirs(output_directory)
    
    output_path = os.path.join(output_directory, 'output.txt') 
    process_file(input_path, output_path)

if __name__ == "__main__":
    main()
