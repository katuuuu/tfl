from dataclasses import dataclass, field
from typing import Callable, Dict, List, Union, Pattern
import re


class Automata:
    def __init__(self, states, init, final, alphabet, map):
        self.states = states
        self.init = init
        self.final = final
        self.alphabet = alphabet
        self.map = map

class LTable:
    def __init__(self, S, E, table, extS, extTable):
        self.S = S
        self.E = E
        self.table = table
        self.extS = extS
        self.extTable = extTable

class MATResult:
    def __init__(self, ok, result):
        self.ok = ok
        self.result = result

class ParsingError(Exception):
    pass
