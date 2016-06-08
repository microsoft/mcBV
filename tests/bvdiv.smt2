(set-logic QF_BV)
(set-info :source |
	Constructed by Aleksandar Zeljic to test bvDiv
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))

(assert (bvule #b0010 b))
(assert (bvule b c))
(assert (= #b0000 (bvudiv #b0000 b)))
(assert (= b (bvudiv b #b0001)))
(assert (= a (bvudiv c b)))
(assert (= c (bvmul a b)))

(check-sat)
(exit)
