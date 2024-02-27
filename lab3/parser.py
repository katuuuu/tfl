import re
from typing import List
from config import config
from typess import Input, ParsingError

REGEX_HEADER = 'regex'
ALPHABET_HEADER = 'alphabet'
MAXLENGTH_HEADER = 'maxlength'


def read_input() -> Input:
    with open(config["inputPath"], "r") as file:
        data = file.read()

    current_stage = ''
    regex_raw = None
    max_length = None
    alphabet = []

    for line in map(str.strip, data.split('\n')):
        if line.lower() in [REGEX_HEADER, ALPHABET_HEADER, MAXLENGTH_HEADER]:
            current_stage = line.lower()
            continue
        if current_stage == REGEX_HEADER:
            regex_raw = line
        elif current_stage == ALPHABET_HEADER:
            alphabet.extend(line.split())
        elif current_stage == MAXLENGTH_HEADER:
            max_length = int(line) if line.isdigit() else None

    if not regex_raw:
        raise ParsingError("You must specify regex")

    regex = re.compile(regex_raw)

    if any(len(v) != 1 for v in alphabet):
        raise ParsingError("Alphabet must contain single characters")

    if max_length is None or not isinstance(max_length, int):
        print("maxLength is not defined and set to default value (10)")
        max_length = 10

    return {
        "alphabet": alphabet,
        "regex": regex,
        "maxLength": max_length
    }
