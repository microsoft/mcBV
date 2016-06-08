(set-logic QF_BV)

(set-info :status sat)

(declare-const X (_ BitVec 4))

(assert (and
			(not (bvslt X #x1))
			(bvslt X #x3)))

(check-sat)
