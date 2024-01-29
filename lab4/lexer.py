import ply.lex as lex

tokens = ('ID', 'PLUS', 'MINUS', 'TIMES', 'LPAREN', 'RPAREN')

t_PLUS = r'\+'
t_TIMES = r'\*'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_ignore = ' \t'
t_MINUS = r'-'

def t_ID(t):
    r'id'
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_emptyline(t):
    r'\n+'
    pass

def t_error(t):
    print(f"Illegal character '{t.value[0]}' at line {t.lineno}")
    t.lexer.skip(1)

lexer = lex.lex()
