from __future__ import annotations
from dataclasses import dataclass

@dataclass
class Constructor:
    name: str
    args: list[Constructor]
    is_variable: bool = False

    def __len__(self):
        return len(self.args)

    def __repr__(self):
        return self.name + ( '(' + ', '.join(map(repr, self.args))+ ')' if self.args else '')


class Rule:
    lhs: Constructor
    rhs: Constructor

    def __init__(self, lhs, rhs) -> None:
        self.lhs, self.rhs = lhs, rhs

    def __repr__(self):
        return f'{self.lhs} -> {self.rhs}'