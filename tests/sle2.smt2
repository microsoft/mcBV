(set-logic QF_BV)
(set-info :status sat)
(declare-fun X () (_ BitVec 3))
(assert (bvsle ((_ sign_extend 1) X) (_ bv0 4)))
(check-sat)

