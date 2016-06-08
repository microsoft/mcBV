(set-logic QF_BV)

(set-info :status sat)

(declare-const X (_ BitVec 8))

(assert (and
			(not (bvslt X #x00))
			(bvslt X #x0F)))
			
(check-sat)
