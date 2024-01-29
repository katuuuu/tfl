from parser import parser
from utils import read_test_cases, write_output
import os

def parse_and_format(input_string):
    cleaned_input = input_string.strip()
    result = parser.parse(cleaned_input)
    return "Parsed: " + str(result) if result else "Parsing Failed"

if __name__ == "__main__":
    input_file_path = "input"
    output_file_path = "output"
    tests_folder = "tests"

    if os.path.exists(input_file_path) and os.path.getsize(input_file_path) == 0:
        test_cases = read_test_cases(tests_folder)
        all_output = ""
        test_number = 1

        for input_string in test_cases:
            formatted_result = parse_and_format(input_string)
            all_output += f"Test {test_number}:\n{formatted_result}\n\n"
            test_number += 1

        write_output(output_file_path, all_output)
    elif os.path.exists(input_file_path):
        with open(input_file_path, 'r') as file:
            input_string = file.read()
        
        formatted_result = parse_and_format(input_string)
        print("============= SLR(1)-разбор слова ============")
        print(formatted_result)
    else:
        print(f"Файл '{input_file_path}' не найден.")
