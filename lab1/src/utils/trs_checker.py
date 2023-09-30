from dataclasses import dataclass
import itertools
import operator

from models.trs_models import Constructor, Rule
from models.linsp_models import *


class TrsChecker:
    variables: set[str]
    rules: list[Rule]
    arity: dict[str, int]

    def __init__(self, v, r) -> None:
        self.variables = v
        self.rules = r
        self.arity = dict()

    def __repr__(self):
        return f'arity: {repr(self.arity)};\nvariables: {self.variables};'

    def check(self):
        for r in self.rules:
            self.check_constructor(r.lhs)
            self.check_constructor(r.rhs)

    def check_constructor(self, c: Constructor):
        if c.is_variable:
            assert c.name in self.variables, f'переменная {c.name} не объявлена'
            return

        assert c.name not in self.variables, f'переменная {c.name} используется как функция'
        if c.name not in self.arity:
            self.arity[c.name] = len(c)
        else:
            assert self.arity[c.name] == len(c)

        for x in c.args:
            self.check_constructor(x)