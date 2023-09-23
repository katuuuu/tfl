(set-logic QF_NIA)

(declare-fun ineq () Bool)
(declare-fun INEQ_2 () Bool)
(declare-fun ineq3 () Bool)
(declare-fun ineq4 () Bool)

(declare-fun combo1 () Bool)
(declare-fun combo2 () Bool)
; comment
(assert (= ineq (> 1 2)))
(assert (= INEQ_2 (> 3 4)))
(assert (= ineq3 (> 6 5)))
(assert (= ineq4 (> 8 7)))

(assert (= combo1 (or ineq ineq3)))
(assert (= combo2 (or INEQ_2 ineq4)))

(assert (= true (and combo1 combo2)))

(check-sat)