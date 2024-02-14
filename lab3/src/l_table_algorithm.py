import re
from typing import Callable, List, Dict, NamedTuple, Pattern
import random
import config

class ParsingError(Exception):
    pass

class Automata:
    def __init__(self, states: int, init: int, final: List[int], alphabet: List[str], map: List[Dict[str, List[int]]]):
        self.states = states
        self.init = init
        self.final = final
        self.alphabet = alphabet
        self.map = map

class LTable:
    def __init__(self, S: List[str], E: List[str], table: List[List[bool]], extS: List[str], extTable: List[List[bool]]):
        self.S = S
        self.E = E
        self.table = table
        self.extS = extS
        self.extTable = extTable

def check_word(word: str, automata: Automata) -> bool:
    current_state = automata.init
    for symbol in word:
        if symbol not in automata.map[current_state]:
            return False
        to_states = automata.map[current_state][symbol]
        if len(to_states) == 0:
            return False
        if len(to_states) > 1:
            raise ParsingError('Automata is not determinate')
        current_state = to_states[0]
    return current_state in automata.final


class Input(NamedTuple):
    regex: Pattern
    alphabet: List[str]
    maxLength: int


class LTableAlgorithm:
    def __init__(self, alphabet: List[str], oracle: Callable[[str], bool], P: int = 100, maxLength: int = 10):
        self.P = P
        self.maxLength = maxLength
        self.checkedWords = []
        self.oracle = oracle
        self.alphabet = alphabet
        self.table = LTable(S=[''], E=[''], table=[], extS=[], extTable=[])
        self.initTable()

    def initTable(self):
        self.table.S = [''] + self.alphabet
        self.table.E = [''] + self.alphabet
        self.table.table = [[self.oracle(s + e) for e in self.table.E] for s in self.table.S]
        self.restructExtended()

    def restructExtended(self):
        self.table.extS = [s + a for s in self.table.S for a in self.alphabet if s + a not in self.table.S]
        self.table.extTable = [[self.oracle(s + e) for e in self.table.E] for s in self.table.extS]

    def isFull(self):
        for ext_row, s in zip(self.table.extTable, self.table.extS):
            if not any(all(row[i] == ext_row[i] for i in range(len(self.table.E))) for row in self.table.table):
                self.table.S.append(s)
                self.table.table.append(ext_row)
                self.restructExtended()
                return False
        return True


    def isCompatable(self):
        for i, row1 in enumerate(self.table.table):
            for j, row2 in enumerate(self.table.table):
                if i >= j: 
                    continue
                if all(row1[k] == row2[k] for k in range(len(self.table.E))): 
                    for a in self.alphabet:
                        s1 = self.table.S[i] + a
                        s2 = self.table.S[j] + a
                        if s1 in self.table.S and s2 in self.table.S:
                            i1 = self.table.S.index(s1)
                            i2 = self.table.S.index(s2)
                            if not all(self.table.table[i1][k] == self.table.table[i2][k] for k in range(len(self.table.E))):
                                self.table.E.append(a)
                                for s in self.table.S:
                                    self.table.table[self.table.S.index(s)].append(self.oracle(s + a))
                                for s in self.table.extS:
                                    self.table.extTable[self.table.extS.index(s)].append(self.oracle(s + a))
                                return False  
        return True 

    def buildAutomata(self):
        states = list(range(len(self.table.S)))
        init = 0
        final = [i for i, row in enumerate(self.table.table) if row[0]] 
        map = [{a: [] for a in self.alphabet} for _ in states]

        for i, s in enumerate(self.table.S):
            for a in self.alphabet:
                next_s = s + a
                next_state = self.table.S.index(next_s) if next_s in self.table.S else None
                if next_state is not None:
                    map[i][a].append(next_state)

        return Automata(states=len(states), init=init, final=final, alphabet=self.alphabet, map=map)

    def MAT(self):
        automata = self.buildAutomata()
        for _ in range(self.P):
            word = ''.join(random.choice(self.alphabet) for _ in range(random.randint(1, self.maxLength)))
            if self.oracle(word) != check_word(word, automata):
                return False, word
        return True, automata

    def compute(self):
        while not self.isFull() or not self.isCompatable():
            pass
        ok, result = self.MAT()
        
        if not ok:
            print(f"Found counterexample: {result}")
        return self.buildAutomata() 
