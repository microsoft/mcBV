module Problem

open System.Collections.Generic
open Microsoft.Z3

type Problem = class
    val mutable goal : Goal
    val mutable vars : HashSet<Expr>    
    val mutable nums : HashSet<Expr>
    val mutable maxVar : int
    val mutable maxNum : int
    val mutable var2expr : Expr[]
    val mutable var2sort : int[]
    val mutable expr2var : Dictionary<Expr, int>
    val mutable num2id : Dictionary<Expr, int>
    val mutable id2num : Expr[]

    new (g, vs, ns, v2e, v2s, e2v, n2i, i2n, mv, mn, dg) = 
        { 
            goal = g;
            vars = vs; 
            nums = ns; 
            maxVar = mv; 
            maxNum = mn;
            var2expr = v2e;
            var2sort = v2s;
            expr2var = e2v;
            num2id = n2i;
            id2num = i2n;
        }

    override this.ToString() = 
        this.goal.ToString()
end