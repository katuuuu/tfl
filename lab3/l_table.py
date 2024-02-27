import math
from typing import List, Callable
from automata import check_word
from typess import ParsingError
import random

class LTableAlgorithm:
    def __init__(self, alphabet: List[str], oracul: Callable[[str], bool], P: int = 100, max_length: int = 10):
        self.P = P
        self.max_length = max_length
        self.checked_words = []
        self.oracul = oracul
        self.alphabet = alphabet
        self.table = {
            'S': [],
            'E': [],
            'table': [],
            'extS': [],
            'extTable': []
        }
        self.init_table()

    def init_table(self):
        self.table = {
            "S": [""] + self.alphabet,
            "E": [""] + self.alphabet,
            "table": [],
            "extS": [],
            "extTable": []
        }
        self.table["table"] = [[self.oracul(s + e) for e in self.table["E"]] for s in self.table["S"]]
        self.restruct_extended()

    def restruct_extended(self):
        self.table["extS"] = [s + a for s in self.table["S"] if not any(s != v and s in v for v in self.table["S"]) for
                              a in self.alphabet]
        self.table["extTable"] = [[self.oracul(s + e) for e in self.table["E"]] for s in self.table["extS"]]

    def compute(self):
        while True:
            while not self.is_full() or not self.is_compatable():
                pass
            res = self.mat()
            if res["ok"]:
                return res["result"]
        return None

    def is_full(self):
        compare_rows = lambda row1, row2: all(v1 == v2 for v1, v2 in zip(row1, row2))
        for i, ext_s in enumerate(self.table['extS']):
            if not any(compare_rows(row, self.table['extTable'][i]) for row in self.table['table']):
                self.table['S'].append(ext_s)
                self.table['table'].append(self.table['extTable'][i])
                self.restruct_extended()
                return False
        return True

    def is_compatable(self):
        compare_rows = lambda row1, row2: all(v1 == v2 for v1, v2 in zip(row1, row2))
        for i in range(len(self.table['S'])):
            for j in range(i + 1, len(self.table['S'])):
                if compare_rows(self.table['table'][i], self.table['table'][j]):
                    for a in self.alphabet:
                        suffix_to_find = self.table['S'][j] + a
                        for idx, s in enumerate(self.table['S']):
                            if s == suffix_to_find:
                                ii = self.table['S'].index(self.table['S'][i])
                                jj = idx
                                if ii < 0 or jj < 0:
                                    continue
                                k = next(
                                    (k for k, (val1, val2) in
                                     enumerate(zip(self.table['table'][ii], self.table['table'][jj]))
                                     if val1 != val2), None)
                                if k is not None:
                                    new_suffix = f"{a}{k}"
                                    self.table['E'].append(new_suffix)
                                    for m, s in enumerate(self.table['S']):
                                        self.table['table'][m].append(self.oracul(f"{s}{new_suffix}"))
                                    for m, s in enumerate(self.table['extS']):
                                        self.table['extTable'][m].append(self.oracul(f"{s}{new_suffix}"))
                                    return False
        return True

    def build_automata(self):
        compare_rows = lambda row1, row2: all(v1 == v2 for v1, v2 in zip(row1, row2))
        states_dict = [row for i, row in enumerate(self.table['table']) if self.table['table'].index(row) == i]
        init_state = states_dict.index([self.oracul(e) for e in self.table['E']])
        if init_state == -1:
            return None
        automata = {
            'states': states_dict,
            'init': init_state,
            'final': [i for i, row in enumerate(self.table['table']) if row[self.table['E'].index('')]],
            'alphabet': self.alphabet,
            'map': [{} for _ in states_dict]
        }
        for from_s in self.table['S']:
            for to_s in self.table['S'] + self.table['extS']:
                if len(to_s) == len(from_s) + 1 and to_s.startswith(from_s):
                    a = to_s[-1]
                    from_row = self.table['table'][self.table['S'].index(from_s)]
                    to_row = self.table['table'][self.table['S'].index(to_s)] if to_s in self.table['S'] else \
                    self.table['extTable'][self.table['extS'].index(to_s) - len(self.table['S'])]
                    add_transition(from_row, to_row, a, automata)
        return automata

    def mat(self):
        automata = self.build_automata()
        if not automata:
            raise ParsingError("Can't build automata")
        for i in range(self.P):
            length = math.floor(1 + random.random() * self.max_length)
            word = ''.join([random.choice(self.alphabet) for _ in range(length)])
            self.checked_words.append(word)
            if self.oracul(word) != check_word(word, automata):
                return {
                    'ok': False,
                    'result': word
                }
        self.checked_words = list(dict.fromkeys(self.checked_words))
        return {
            'ok': True,
            'result': automata
        }


def add_transition(from_row, to_row, a, automata):
    from_state = automata['states'].index(from_row)
    to_state = automata['states'].index(to_row)

    if a not in automata['map'][from_state]:
        automata['map'][from_state][a] = []

    if to_state not in automata['map'][from_state][a]:
        automata['map'][from_state][a].append(to_state)


# перепиши класс LTableAlgorithm в рабочее состояние


