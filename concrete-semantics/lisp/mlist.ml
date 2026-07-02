

(* given some form of expression *)
type expr =
  | Var         
  | Const of int
  | Add of expr * expr
  | Mult of expr * expr
  | VarPow of int


let rec mlist2 (xs : int list) (pow : int) : expr =
  match xs with
  | [] -> Mult(Const 0, VarPow 0)  (*dummy value*)
  | [x] -> mlist3 x pow
  | (x :: tt) -> let v =  mlist3 x pow
                 and v2 = mlist2 tt (pow+1) in   
                    Add(v,v2)
  and mlist3 (x : int) (pow : int) : expr =
    if pow < 1 then Mult(Const x, VarPow 0)
    else Mult(Const x, VarPow pow)
    
let mlist (xs : int list) : expr = mlist2 xs 0 


