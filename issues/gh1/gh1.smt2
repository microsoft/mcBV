(set-logic QF_BV)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))

(assert (bvugt a #x0000A000))
(assert (bvugt b #x0000A000))
(assert (bvuge c #xFFFFFFF0))

(assert (= c (bvmul a b)))

(check-sat)
