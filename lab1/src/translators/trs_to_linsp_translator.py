from models.trs_models import Constructor, Rule
from models.linsp_models import Variable, Param, Factor, LinComb


class LinspTranslator:

    @staticmethod
    def trs_to_linsp(rules: list[Rule], variables):
            return [
                (LinspTranslator.constructor_to_linsp(r.lhs, variables), LinspTranslator.constructor_to_linsp(r.rhs, variables))
                for r in rules
            ]

    @staticmethod
    def constructor_to_linsp(c: Constructor, variables: set[str]) -> LinComb:
        '''
        вызов каждого конструктора (в т.ч. и переменной) 
        будем представлять линейной комбинацией

        f(arg1, arg2, .. , argn) -> f_1*arg1 + f_2*arg2 + ... + f_n*argn + f_{n+1}*e
        x -> 1*x

        не забываем, что композиция линейны отображений - есть линейное отображение, 
        поэтому никаких поверхностей 2+ порядка тут не возникнет 
        '''

        
        if c.is_variable:
            # переменную x возвращаем как 1x + 0I
            return LinComb([
                Factor([Param.one()],Variable(c.name)),
                Factor([Param.zero()],Variable.identity()),
                ])

        arity = len(c)
        # params: [f_1, f_2, ... ,f_n, f_{n+1}]
        # коэффициенты линейной функции - по одному для каждого аргумента
        params = [Param(c.name, i) for i in range(1, arity+2)]
        # elems: [arg1, arg2, ... ,arn, e]
        e_lin_comb = LinComb([Factor([Param.one()],Variable.identity())]) # свободный член = 1I
        elems = [LinspTranslator.constructor_to_linsp(x, variables) for x in c.args] + [e_lin_comb] # c1 + c2 + .. + cn + 1I
        # теперь скалярно перемножаем
        lin_combs = [elem.mult_by_param(p) for (p,elem) in zip(params, elems)]
        return sum(lin_combs, start=LinComb.empty_lin_comb())