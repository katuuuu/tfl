import re
from typing import List, Union, Dict


class ParsingError(Exception):
    def __init__(self, message: str):
        super().__init__(message)


class Input:
    def __init__(self, regex: re.Pattern, alphabet: List[str], max_length: int):
        self.regex = regex
        self.alphabet = alphabet
        self.max_length = max_length


class LTable:
    def __init__(self, S: List[str], E: List[str], table: List[List[bool]], extS: List[str],
                 extTable: List[List[bool]]):
        self.S = S
        self.E = E
        self.table = table
        self.extS = extS
        self.extTable = extTable


class MATResult:
    def __init__(self, ok: bool, result: Union[str, 'Automata']):
        self.ok = ok
        self.result = result


class Automata:
    def __init__(self, states: int, final: List[int], init: int, alphabet: List[str],
                 automata_map: List[Dict[str, List[int]]]):
        self.states = states
        self.final = final
        self.init = init
        self.alphabet = alphabet
        self.map = automata_map
