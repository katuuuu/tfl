from uuid import uuid4
from pprint import pp

from models.linsp_models import LinComb, Param, Variable
from models.ineq_models import Ineq, IneqSort
from models.ineq_models import IneqSystem, IneqSystemSort

class IneqTranslator:

    @staticmethod
    def rule_to_ineq_sys(rule: tuple[LinComb, LinComb]):
        '''
        принимает Tuple[L1: LinComb, L2: LinComb]
        возвращает Tuple[S1: IneqSystem, S2: IneqSystem],
        где S1 и S2 - системы неравенств, описывающие утверждение L1 > L2
        в S1 строгое неравенство по свободному члену и нестрокое по всем переменным
        в S2 - наоборот
        '''
        d1, d2 = rule[0].to_dict(), rule[1].to_dict()
        dk1, dk2 = set(d1.keys()), set(d2.keys())
        
        # формально, если x in {LHS.vars}\{RHS.vars}
        # то в RHS x стоит с нулевым коэффициентом
        intersect = dk1.intersection(dk2).difference({Variable.identity()})
        only_left = dk1.difference(dk2)
        only_right = dk2.difference(dk1)

        # создадим множество неравенств
        ineq_sys = IneqSystem.empty()
        for coef in intersect:
            # в обеих частях правила
            ineq_sys.add(Ineq(d1[coef], d2[coef], IneqSort.NONE))
        for coef in only_left:
            # с нулевым коэффициентом справа
            ineq_sys.add(Ineq(d1[coef], [[Param.zero()]], IneqSort.NONE)) 
        for coef in only_right:
            # с нулевым коэффициентом слева
            ineq_sys.add(Ineq([[Param.zero()]], d2[coef], IneqSort.NONE)) 
        # свободные члены отдельно
        ineq_sys.set_e(
            Ineq(d1[Variable.identity()], d2[Variable.identity()], IneqSort.NONE)
        )
            
        return (
            ineq_sys.get_sorted(IneqSystemSort.BY_E), 
            ineq_sys.get_sorted(IneqSystemSort.BY_VARS)
        ) 

    @staticmethod
    def linsp_to_ineq(rules: list[tuple[LinComb, LinComb]]):
        return  list(map( 
            IneqTranslator.rule_to_ineq_sys,
            rules
        ))