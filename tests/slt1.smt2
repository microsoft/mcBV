(set-logic QF_BV)

(set-info :status sat)

(declare-const X (_ BitVec 8))

(assert (and
			(= X #x01)
			(bvslt X #x0F)))

(check-sat)
