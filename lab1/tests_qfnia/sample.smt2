(set-logic QF_NIA)

; объявления коэффициентов линейных функций

(declare-fun f1 () Integer)
(declare-fun f2 () Integer)
(declare-fun f3 () Integer)
(declare-fun g1 () Integer)
(declare-fun g2 () Integer)
(declare-fun g3 () Integer)

; объявления систем

(declare-fun sys1 Bool)
(declare-fun sys1_e () Bool)
(declare-fun sys1_var () Bool)

(declare-fun sys2 Bool)
(declare-fun sys2_e () Bool)
(declare-fun sys2_var () Bool)

; вычисление неравенств в системах

(assert (= 
            sys1_var 
            (and 
                (f1 > g1)
                (f2 > g2)
                (f3 >= g3))
))

(assert (= sys1_e
            (and 
                (f1 >= g1)
                (f2 >= g2)
                (f3 > g3))
))

; вычисление систем

(assert (= sys1 (or sys1_e sys1_var)))
(assert (= sys2 (or sys2_e sys2_var)))

; глобальное вычисление
(assert (and sys1 sys2))

(check-sat)