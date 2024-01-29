import ply.yacc as yacc
from lexer import tokens

def p_expression_plus(p):
    'E : E PLUS T'
    p[0] = (p[1], '+', p[3])

def p_expression_e_t(p):
    'E : T'
    p[0] = p[1]

def p_term_times(p):
    'T : T TIMES F'
    p[0] = (p[1], '*', p[3])

def p_term_f(p):
    'T : F'
    p[0] = p[1]

def p_factor_expr(p):
    'F : LPAREN E RPAREN'
    p[0] = p[2]

def p_factor_id(p):
    'F : ID'
    p[0] = ('id',)

def p_error(p):
    if p:
        print(f"Syntax error at '{p.value}' at line {p.lineno}")
    else:
        print("Syntax error at EOF")

parser = yacc.yacc()
