import re


SKIP = 'SKIP'
COMMENT = SKIP
SPACE = SKIP

VARKW = 'VARKW'
ARROW = 'ARROW'
EQ = 'EQ'
COMMA = 'COMMA'
LP = 'LP'
RP = 'RP'
IDENT = 'IDENT'

LEXEM_TYPES = [
    (VARKW, r'^variables', lambda x: None),
    (ARROW, r'^\:\:\=', lambda x: None),
    (EQ, r'^\=', lambda x: None),
    (COMMA, r'^\,', lambda x: None), 
    (LP, r'^\(', lambda x: None),
    (RP, r'^\)', lambda x: None),
    (IDENT, r'^[A-Za-z]', lambda x: x),
    (COMMENT, r'^\#[^\n]*', lambda x: None),
    (SPACE, r'^\s', lambda x: None),
]