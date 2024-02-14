import re
from typing import NamedTuple, Pattern, List

class ParsingError(Exception):
    pass

class Input(NamedTuple):
    regex: Pattern
    alphabet: List[str]
    maxLength: int

def read_input(input_path: str) -> Input:
    with open(input_path, 'r') as file:
        data = file.read().split('\n')

    regex_raw = None
    alphabet = []
    max_length = 10  

    current_section = ''
    for line in data:
        if 'alphabet' in line.lower():
            current_section = 'alphabet'
            continue
        elif 'regex' in line.lower():
            current_section = 'regex'
            continue
        elif 'maxlength' in line.lower():
            current_section = 'maxlength'
            continue

        if current_section == 'alphabet' and line.strip():
            alphabet.extend(line.strip().split(' '))
        elif current_section == 'regex' and line.strip():
            regex_raw = line.strip()
        elif current_section == 'maxlength' and line.strip():
            max_length = int(line.strip())

    if not regex_raw:
        raise ParsingError("You must specify regex")

    regex = re.compile(regex_raw)
    if any(len(v) != 1 for v in alphabet):
        raise ParsingError("Alphabet must contain single characters")

    return Input(regex=regex, alphabet=alphabet, maxLength=max_length)
