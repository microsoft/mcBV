(set-logic QF_BV)
(set-info :status sat)
(declare-fun X () (_ BitVec 4))
(assert (bvsle ((_ sign_extend 2) X) (_ bv0 6)))
(check-sat)

