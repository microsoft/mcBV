(set-logic QF_BV)
(set-info :source |
	Constructed by Aleksandar Zeljic
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))


(assert (bvult b #b0101))
(assert (bvult a #b0011))
(assert (bvugt c #b1000))
(assert (= c (bvadd a b)))
(check-sat)
(exit)
