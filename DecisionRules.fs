module DecisionRules

open System.Numerics
open GlobalOptions
open Util
open Literal
open Clause
open BooleanValuation
open Trail
open State
open BitVector
open Learning
open Explain
open Interval
open Bit


let bDecide (s:State) (l:Literal) =
    verbose <| (lazy sprintf "Decide %d" l)
    assert(not s.IsConflicted)
    assert ((!s.bVal).getValueB l = Undefined)
    s.Push (BoolDecision l)
    assert((!s.theoryDB).isDefined (lit2var l) || not s.IsConflicted)


let implyDecision (s:State) (bvVar:Var) (newValue:BitVector) =
    let oldValue = (!s.bvVal).getValue bvVar
    let newRel = getModelAssignmentPredicate s.database bvVar newValue s.bVal s.bvVal s.bounds
    let b = newRel.getBoolVar
    let is_more_concrete = newValue.isMoreConcreteThan oldValue

    match (!s.bVal).getValueB (b) with
    | True -> true

    | Undefined when is_more_concrete ->
        s.Push (BoolDecision b)
        true

    | Undefined -> // when not is_more_concrete
        UNREACHABLE("Decisions must be more concrete.")
        false

    | False ->
        false


let refineBitPattern (bnds_value:Interval) (pattern:BitVector) finished step (bit:Bit) =

    let mutable to_decide = None
    let mutable q = None

    assert(step <> 0)
    let refined_pattern = BitVector.changeBits true bit pattern (finished + step - 1) step
    assert(not (finished + step = pattern.Length) || refined_pattern.isConcreteValue)

    if refined_pattern.isConcreteValue then
        if bnds_value.Contains refined_pattern then
            to_decide <- Some (refined_pattern)
        else
            if step > 1 then
                q <- Some (pattern, finished, step/2)
            else // Step is too small
                ()
    else
        let ref_pat_int = bnds_value.Intersection (Interval (refined_pattern.Minimum, refined_pattern.Maximum))

        if ref_pat_int.isSingleton then
            to_decide <- Some (ref_pat_int.Lower)
        elif ref_pat_int.isEmpty then
            // Current refinment of the pattern does not fit the bounds,
            // attempt to reduce the refinement step or give up on this branch.
            if step > 1 then
                q <- Some (pattern, finished, step/2)
            else // Step is too small
                ()
        else
            // advance the search on the current branch
            let newFinished = finished + step
            let newStep = refined_pattern.Length - newFinished
            q <- Some (refined_pattern, newFinished, newStep)
            assert (newStep <> 0)
            assert (newStep + newFinished <= refined_pattern.Length)

    assert (not (to_decide.IsSome && q.IsSome))
    (to_decide, q)

let bitpatternDecide (s:State) (bvVar:Var) (rle_value:BitVector) (bnds_value:Interval) =
    let mutable decided = false
    let mutable num_attmpts = 0

    let prefix = BitVector.getCommonPrefix bnds_value.Lower bnds_value.Upper
    let mutable set = BitVector.Intersect rle_value prefix

    if set.isInvalid then // Conflict involves only pattern and the bounds AZ: This check should be done elsewhere?
        let maex = ((!s.bvVal).getExplanation bvVar)
        let (lex, uex) = ((!s.bounds).getExplanations bvVar)
        assert(maex <> lex && maex <> lex) // AZ: This conflict should be caught elsewhere
        let cnflct = newClauseFromList(if lex = uex then
                                            [Negate maex; Negate lex]
                                        else
                                            [Negate maex; Negate uex; Negate lex])
        s.SetConflict (Some (ref cnflct))
    else
        let dimension = set.estimateSearchSpace()

        if dimension = 0 then
            assert(set.isConcreteValue)
            decided <- implyDecision s bvVar set
        else
            let gray_code (n:BitVector) =
                BitVector.bvXOR n (BitVector.bvLShiftRight n (BitVector.One n.Length))

            let mutable cnt = BitVector.AllZero dimension
            let mutable overflown = false

            while not decided && not overflown do
                let candidate = BitVector.meld set (gray_code cnt)
                if bnds_value.Contains candidate then
                   num_attmpts <- num_attmpts + 1
                   if (implyDecision s bvVar candidate) then
                        let na = num_attmpts
                        dbg <| (lazy sprintf " | (Decided on %d:bv with T:%s and TBnds:%s after %d attempts.)" bvVar (rle_value.ToString()) (bnds_value.ToString()) na)
                        decided <- true

                cnt <- BitVector.bvAdd cnt (BitVector.One dimension)
                overflown <- BitVector.isAllZero cnt

        if not decided then
                // CMW: Empty domains are detected during decision making,
                // if, for some time, an empty-domain variable is not chosen,
                // we will detect the conflict much later. We should try
                // to find a cheaper/quicker way of determining empty domains.
                // AZ: Empty domain is a conflict and will be detected during
                //     regular search if it is possible to determine that.
                //     This is only in the case where the domain is empty but it
                //     is not trivial to notice it.
                verbose <| (lazy sprintf "> The domain of %d:bv is empty." bvVar)
                let cflct = explainEmptyDomain s bvVar // TODO: We can collect all the reasons for conflict while trying to make a decision.
                s.SetConflict (Some (ref cflct))


let arithmeticDecide (s:State) (bvVar:Var) (rle_value:BitVector) (bnds_value:Interval) =
    assert (bvVar <> 0)
    assert (rle_value.Length > 0)
    let sort = rle_value.Length

    let two = BigInteger 2

    let intersection = bnds_value.Intersection (Interval (rle_value.Minimum, rle_value.Maximum))

    if intersection.isEmpty then // Conflict involves only bounds and the pattern. AZ: This check should be done elsewhere?
        let maex = ((!s.bvVal).getExplanation bvVar)
        let (lex,uex) =  ((!s.bounds).getExplanations bvVar)
        assert(maex <> lex && maex <> lex) // AZ: This conflict should be caught elsewhere
        let cnflct = newClauseFromList( if lex = uex then [Negate maex; Negate lex] else [Negate maex; Negate uex; Negate lex])
        s.SetConflict (Some (ref cnflct))
    else
        let (lVal, uVal) = (intersection.Lower, intersection.Upper)

        let mutable decided = false
        let mutable num_attmpts = 0

        let mutable q = [(lVal, uVal)]

        while q <> [] do
            let (lb, ub) = q.Head
            q <- q.Tail
            let cur = BitVector.bvExtract (sort-1) 0
                        (BitVector.bvAShiftRight (BitVector.bvAdd
                                                     (BitVector.bvZeroExtend lb 1)
                                                     (BitVector.bvZeroExtend ub 1))
                                                 (BitVector.One sort))
            assert(BitVector.bvULEQ lb cur)
            assert(BitVector.bvULEQ cur ub)
            num_attmpts <- num_attmpts + 1
            if  (rle_value.Contains cur) &&
                (bnds_value.Contains cur) &&
                (implyDecision s bvVar cur) then
                let na = num_attmpts
                dbg <| (lazy sprintf " | (Decided on %d:bv with T:%s and TBnds:%s after %d attempts.)" bvVar (rle_value.ToString()) (bnds_value.ToString()) na)
                decided <- true
                q <- []
            else
                let newUpperBound = BitVector.bvSub cur (BitVector.One sort)
                let newLowerBound = BitVector.bvAdd cur (BitVector.One sort)

                if BitVector.bvULEQ lb newUpperBound then
                    q <- [(lb, newUpperBound)] @ q

                if BitVector.bvULEQ newLowerBound ub then
                    q <- [(newLowerBound, ub)] @ q

        if not decided then
            // CMW: Empty domains are detected during decision making,
            // if, for some time, an empty-domain variable is not chosen,
            // we will detect the conflict much later. We should try
            // to find a cheaper/quicker way of determining empty domains.
            // AZ: Empty domain is a conflict and will be detected during
            //     regular search if it is possible to determine that.
            //     This is only in the case where the domain is empty but it
            //     is not trivial to notice it.
            verbose <| (lazy sprintf "> The domain of %d:bv is empty." bvVar)
            let cflct = explainEmptyDomain s bvVar // TODO: We can collect all the reasons for conflict while trying to make a decision.
            s.SetConflict (Some (ref cflct))


// CMW: This is the general tDecide that may use all theories.
let tDecide (s:State) (bvVar:Var) =
    assert (bvVar <> 0)

    let rle_value = (!s.bvVal).getValue bvVar // <-- uses partial assignments (pPAs)
    let bnds_value = (!s.bounds).get bvVar // <-- also uses bounds
    let bp_space_size = rle_value.estimateSearchSpace()
    let interval_space_size = bnds_value.estimateSearchSpace()

    if USE_BOUNDS && interval_space_size < bp_space_size then
        arithmeticDecide s bvVar rle_value bnds_value
    else
        bitpatternDecide s bvVar rle_value bnds_value



let chooseVariable (s:State) : Var =
    let mutable chosen = false
    let mutable v = 0

    while not chosen do
        v <- (!s.variableDB).varOrder.next()
        if (!s.variableDB).getBitVectorLength v > 0 then
            if not ((!s.bvVal).getValue v).isConcreteValue then
                chosen <-true
        else
            if (!s.bVal).getValueB v = Undefined then
                chosen <- true
    v


let decide (s:State) =
    assert (not s.variableDB.Value.varOrder.IsEmpty)
    let pSorts = (ref (!s.variableDB).sorts)
    let mutable decided = false
    let mutable v = chooseVariable s
    let mutable is_bv = (!pSorts).[lit2var v] > 0

    while not decided do

        if is_bv then
            assert (not ((!s.bvVal).getValue v).isConcreteValue)
            verbose <| (lazy sprintf "> Making a Model assignment.")
            decided <- true
            tDecide s v

        if not is_bv then
            assert (((!s.bVal).getValueB v) = Undefined)
            verbose <| (lazy sprintf "> Making a Boolean decision.")
            decided <- true
            bDecide s v

        if not decided then
            v <- chooseVariable s
            is_bv <- (!pSorts).[lit2var v] > 0
