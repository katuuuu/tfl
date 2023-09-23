from operator import methodcaller
import itertools
from dataclasses import dataclass
from pprint import pp

from models.ineq_models import Ineq, IneqSort
from models.ineq_models import IneqSystem, IneqSystemSort
from models.linsp_models import Param


@dataclass
class SmtIneq:
    sign: str
    lhs: list[str]
    rhs: list[str]

    def smt2_str(self):
        return f'({self.sign} (* {" ".join(self.lhs)}) (* {" ".join(self.rhs)}))'


@dataclass
class SmtIneqSystem:
    name: str
    ineqs: list[SmtIneq]


@dataclass
class SmtTwinSystem:
    name: str
    sys1: SmtIneqSystem
    sys2: SmtIneqSystem


class SmtTranslator:
    systems_counter: int = 0
    params: set[str]
    twin_systems: list[SmtTwinSystem]
    
    def use_counter(self) -> str:
        self.systems_counter+=1
        return str(self.systems_counter)

    def extract_params(self, twin_systems: list[tuple[IneqSystem, IneqSystem]]) -> set[str]:
        systems = [x[0] for x in twin_systems]

        ineqs = itertools.chain.from_iterable(map(
            methodcaller('get_all_ineqs'), 
            systems
        ))

        params = set(itertools.chain.from_iterable(map(
            methodcaller('get_all_params'), 
            ineqs
        )))

        params = filter(lambda x: x not in {Param.zero(), Param.one()}, params)

        return set([p.repr2() for p in params])
    
    def ineq_to_smt(self, ineq: Ineq) -> SmtIneq:
        return SmtIneq(
            ineq.sign_str(), 
            [p.repr2() for p in ineq.lhs], 
            [p.repr2() for p in ineq.rhs])

    def ineq_sys_to_smt(self, system: IneqSystem, name) -> SmtIneqSystem:
        return SmtIneqSystem(
            name,
            [self.ineq_to_smt(ineq) for ineq in system.get_all_ineqs()]
        )

    def build_smt_repr(self, twin_systems: list[tuple[IneqSystem, IneqSystem]]):
        # смотрим, какие есть коэффициенты в уравнениях 
        self.params = self.extract_params(twin_systems)

        twins_in_smt = []
        for ts in twin_systems:
            base_name = f'sys{self.use_counter()}' 
            sys1 = self.ineq_sys_to_smt(ts[0], f'{base_name}_e')
            sys2 = self.ineq_sys_to_smt(ts[1], f'{base_name}_var')
            twins_in_smt.append(SmtTwinSystem(base_name, sys1, sys2))

        self.twin_systems = twins_in_smt

        return self

    def record_to_file(self, file: str):
        with open(file, 'w') as f:
            f.write(self.smt2_str())

    def print_smt2(self):
        print(self.smt2_str())

    def smt2_str(self):
        ident1 = ' '*11
        ident2 = ' '*12

        res = ''
        res += '(set-logic QF_NIA)\n\n'
        res += '; объявления коэффициентов линейных функций\n\n'

        for x in self.params:
            res += f'(declare-fun {x} () Int) \n'

        res += '\n'
        res += '; объявления систем\n\n'
        for x in self.twin_systems:
            res +=f'(declare-fun {x.name} () Bool)\n'
            res +=f'(declare-fun {x.sys1.name} () Bool)\n'
            res +=f'(declare-fun {x.sys2.name} () Bool)\n'
        res += '\n'

        res += '; монотонность (точнее строгое возрастание) по каждому аргументу\n\n'
        for x in self.params:
            res += f'(assert (> {x} 0)) \n'
        res += '\n'

        res += '; вычисление систем\n\n'
        for x in self.twin_systems:
            for s in [x.sys1, x.sys2]:
                res += f'(assert (= '
                res += s.name + '\n'
                res += ident1 + '(and' 
                for ineq in s.ineqs:
                    res += '\n' + ident2 + ineq.smt2_str()
                # res += '\n'
                res += ')))\n\n'

        res += '; вычисление пар систем\n\n'
        for x in self.twin_systems:
            res += f'(assert (= {x.name} (or {x.sys1.name} {x.sys2.name})))\n\n'

        res += '; вычисление выполнения всех пар систем\n\n'
        res += f'(assert (= true (and {" ".join([x.name for x in self.twin_systems])})))\n\n'

        res += '(check-sat)'
        return res

