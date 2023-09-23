from dataclasses import dataclass


@dataclass
class Param:
    name: str
    index: int

    def __repr__(self):
        return f'{self.name}{chr(int("2080", base=16) + self.index)}'


    def repr2(self) -> str:
        if self == Param.zero():
            return '0'

        if self == Param.one():
            return '1'

        return f'{self.name}{self.index}'

    def __hash__(self) -> int:
        return hash(repr(self))

    @staticmethod
    def zero():
        return Param('0', -int("2080", base=16))

    @staticmethod
    def one():
        return Param('1', -int("2080", base=16))


@dataclass
class Variable:
    value: str

    def __repr__(self):
        return self.value
    
    def __hash__(self):
        return ord(self.value[0])
    
    @staticmethod
    def identity():
        return Variable('𝛪')


@dataclass
class Factor:
    coefs: list[Param]
    variable: Variable

    def __repr__(self):
        return ''.join(map(repr, self.coefs + [self.variable]))

    def mult_by_param(self, p: Param):
        return Factor([p] + self.coefs, self.variable)


@dataclass
class LinComb:
    '''
    рассморим выражение: a1a2*x + b1*y + c1
    его траутуем как: a1a2*x + b1*y + c1*e
    тут есть:
        * Variables: x, y, e
        * Params: a1, a2, b1, c1
        * Factors: ([a1,a2], x), ([b1], y), ([c1], e)
        * LinCombs: [([a1,a2], x), ([b1], y), ([c1], e)]
    '''

    factors: list[Factor]

    def __repr__(self):
        return ' + '.join(map(repr, self.factors))
    
    def __add__(self, o):
        assert type(o) == LinComb
        return LinComb(self.factors + o.factors)

    def mult_by_param(self, p: Param):
          return LinComb([
                f.mult_by_param(p)
                for f in self.factors
            ])

    @staticmethod
    def empty_lin_comb():
        return LinComb([])

    def regularize(self):
        # берем все переменные из этой линейной комбинации
        fset = set(map(lambda x: x.variable, self.factors))
        # группируем по переменным
        d : dict[Variable, list[Param]] = dict((f, []) for f in fset)
        for factor in self.factors:
            d[factor.variable] += factor.coefs
        self.factors = [Factor(coefs, variable) for variable, coefs in d.items()]
        return self

    def to_dict(self):
        self.regularize()
        return dict(
            (f.variable, f.coefs)
            for f in self.factors
        )