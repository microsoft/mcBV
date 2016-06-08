(set-logic QF_BV)
(set-info :status sat)
(declare-fun X () (_ BitVec 8))
(assert (bvsle ((_ zero_extend 3) X) (_ bv0 11)))
(check-sat)

