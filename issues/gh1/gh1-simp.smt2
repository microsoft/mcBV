(set-logic QF_BV)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
;;(declare-fun c () (_ BitVec 8))

(assert (bvugt a #x0A))
(assert (bvugt b #x0A))
;;(assert (bvuge c #xF0))
;;(assert (= c (bvmul a b)))

(check-sat)
;; (get-model)
