from parser.praser_config import *
from parser.lexer import *
from models.trs_models import Constructor, Rule


class Parser:
    file: str

    tokens: list[Token]
    cur_type: str
    cur_val: str

    stack: list[Constructor]

    variables: set[str]
    rules: list[Rule]

    def __init__(self, file: str):
        self.file = file

    def lexemize(self):
        tokens = lexer(self.file) + [Token('None', 'None')]
        self.cur_type = tokens[0].typ
        self.cur_val = tokens[0].value
        self.tokens = tokens[1:]
        return self
    
    def parse(self):
        self.stack = []
        self.variables = set()
        self.rules = []
        return self._parse_all()

    def _next(self):
        if len(self.tokens) == 0:
            raise RuntimeError('невозможно вытащить следующий токен')
        self.cur_val, self.cur_type, self.tokens = \
            self.tokens[0].value, self.tokens[0].typ , self.tokens[1:]

    def _err(self):
        raise RuntimeError(
            f'последовательность токенов не соответствует грамматике: {self.tokens[10:]}...'
        )

    def _check_and_shift(self, typ):
        if self.cur_type != typ:
            self._err()
        self._next()

    def _parse_all(self):
        self._parse_vars()
        self._parse_rules()
        assert len(self.tokens) == 0
        return self.rules, self.variables 
    
    def _parse_vars(self):
        self._check_and_shift(VARKW)
        self._check_and_shift(EQ)

        if self.cur_type != IDENT:
            self._err()

        self._parse_variables()

        while self.cur_type == COMMA:
            self._next()
            self._parse_variables()

    def _parse_variables(self):
        if self.cur_type != IDENT:
            self._err()

        self.variables.add(self.cur_val)
        self._next()

    def _parse_rules(self):
        while self.cur_type == LP:
            self._parse_rule()

    def _parse_rule(self):
        self._check_and_shift(LP)
        lhs = self._parse_constructor()
        self._check_and_shift(ARROW)
        rhs = self._parse_constructor()
        self._check_and_shift(RP)

        self.rules.append(Rule(lhs, rhs))

    def _parse_constructor(self) -> Constructor:
        name = self._parse_name()
        args = []
        is_variable_flag = True
        if self.cur_type == LP:
            is_variable_flag = False
            self._check_and_shift(LP)
            args = self._parse_args()
            self._check_and_shift(RP)

        c = Constructor(name, args, is_variable_flag)
        return c

    
    def _parse_name(self):
        if self.cur_type != IDENT:
            self._err()
        name = self.cur_val
        self._next()
        return name

    def _parse_args(self) -> list[Constructor]:
        args = []
        if self.cur_type == IDENT:
            args.append(self._parse_constructor())
            while self.cur_type == COMMA:
                self._next()
                args.append(self._parse_constructor())
        return args