from models.trs_models import Constructor, Rule
from models.linsp_models import Variable, Param, Factor, LinComb


class LinspTranslator:

    @staticmethod
    def trs_to_linsp(rules: list[Rule]):
            return [
                (LinspTranslator.constructor_to_linsp(r.lhs), LinspTranslator.constructor_to_linsp(r.rhs))
                for r in rules
            ]

    @staticmethod
    def constructor_to_linsp(c: Constructor) -> LinComb:
        '''
        вызов каждого конструктора (в т.ч. и переменной) 
        будем представлять линейной комбинацией

        f(arg1, arg2, .. , argn) -> f_1*arg1 + f_2*arg2 + ... + f_n*argn + f_{n+1}*e
        x -> 1*x

        не забываем, что композиция линейны отображений - есть линейное отображение, 
        поэтому никаких поверхностей 2+ порядка тут не возникнет 
        '''

        if c.is_variable():
            return LinComb([
                Factor([Param.one()],Variable(c.name)),
                Factor([Param.zero()],Variable.identity()),
                ])


        arity = len(c)
        
        # params: [f_1, f_2, ... ,f_n, f_{n+1}]
        params = [Param(c.name, i) for i in range(1, arity+2)]
        # elems: [arg1, arg2, ... ,arn, e]
        e_lin_comb = LinComb([Factor([],Variable.identity())])
        elems = [LinspTranslator.constructor_to_linsp(x) for x in c.args] + [e_lin_comb]
        # теперь скалярно перемножаем
        lin_combs = [elem.mult_by_param(p) for (p,elem) in zip(params, elems)]
        return sum(lin_combs, start=LinComb.empty_lin_comb()).regularize()