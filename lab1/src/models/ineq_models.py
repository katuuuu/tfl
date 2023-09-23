from dataclasses import dataclass
from enum import IntEnum
from copy import deepcopy

from models.linsp_models import Param


IneqSort = IntEnum('IneqSort', ['NONE', 'STRICT', 'EASY'])
IneqSystemSort = IntEnum('IneqSystemSort', ['NONE', 'BY_E', 'BY_VARS'])


@dataclass
class Ineq:
    lhs: list[Param]
    rhs: list[Param]
    sort: IneqSort
    
    def __repr__(self):
        return f'({self.lhs} {self.sign_str()} {self.rhs})'

    def sign_str(self):
        return {
            IneqSort.NONE: '>?',
            IneqSort.STRICT: '>',
            IneqSort.EASY: '>='
        }[self.sort]

    @staticmethod
    def empty():
        return Ineq([], [], IneqSort.NONE)

    def get_sorted(self, sort: IneqSort):
        sorted_ineq = deepcopy(self)
        sorted_ineq.sort = sort
        return sorted_ineq

    def get_all_params(self):
        return self.lhs + self.rhs


@dataclass
class IneqSystem:
    by_e: Ineq
    by_vars: list[Ineq] 
    sort: IneqSystemSort

    def __repr__(self):
        return '(and ' + ' '.join(map(repr, self.by_vars)) + ' ' + repr(self.by_e) + ')'

    def __hash__(self):
        return hash(str(self.by_e))

    @staticmethod
    def empty():
        return IneqSystem(Ineq.empty(), [], IneqSystemSort.NONE)

    def add(self, x: Ineq):
        self.by_vars.append(x)
    
    def set_e(self, x: Ineq):
        self.by_e = x

    def get_sorted(self, sort: IneqSystemSort):
        system = deepcopy(self)
        
        # определяяем виды неравенств в системе 
        if sort == IneqSystemSort.BY_E:
            e_sort, vars_sort = IneqSort.STRICT, IneqSort.EASY
        else:
            e_sort, vars_sort = IneqSort.EASY, IneqSort.STRICT

        # задаем строгость неравенств в системе
        system.by_vars = list(map(
            lambda x: x.get_sorted(vars_sort), 
            system.by_vars
        ))
        system.by_e = system.by_e.get_sorted(e_sort)

        return system

    def get_all_ineqs(self):
        return self.by_vars + [self.by_e]