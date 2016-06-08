(set-logic QF_BV)
(set-info :status sat)

(declare-fun X () (_ BitVec 4))

(assert (bvule #b100000 ((_ sign_extend 2) X)))
;; sat e.g., when (= X #x8)

(check-sat)
