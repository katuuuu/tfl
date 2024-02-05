
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'ID LPAREN MINUS PLUS RPAREN TIMESE : E PLUS TE : TT : T TIMES FT : FF : LPAREN E RPARENF : ID'
    
_lr_action_items = {'LPAREN':([0,4,6,7,],[4,4,4,4,]),'ID':([0,4,6,7,],[5,5,5,5,]),'$end':([1,2,3,5,9,10,11,],[0,-2,-4,-6,-1,-3,-5,]),'PLUS':([1,2,3,5,8,9,10,11,],[6,-2,-4,-6,6,-1,-3,-5,]),'RPAREN':([2,3,5,8,9,10,11,],[-2,-4,-6,11,-1,-3,-5,]),'TIMES':([2,3,5,9,10,11,],[7,-4,-6,7,-3,-5,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'E':([0,4,],[1,8,]),'T':([0,4,6,],[2,2,9,]),'F':([0,4,6,7,],[3,3,3,10,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> E","S'",1,None,None,None),
  ('E -> E PLUS T','E',3,'p_expression_plus','parser.py',5),
  ('E -> T','E',1,'p_expression_e_t','parser.py',9),
  ('T -> T TIMES F','T',3,'p_term_times','parser.py',13),
  ('T -> F','T',1,'p_term_f','parser.py',17),
  ('F -> LPAREN E RPAREN','F',3,'p_factor_expr','parser.py',21),
  ('F -> ID','F',1,'p_factor_id','parser.py',25),
]
