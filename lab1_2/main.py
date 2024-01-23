import os
from domino_test_processor import process_tests

test_folder = 'tests'
output_folder = 'results'

if not os.path.exists(output_folder):
    os.makedirs(output_folder)

process_tests(test_folder, output_folder)
