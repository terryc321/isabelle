

(* given some form of expression *)
type expr =
  | Var         
  | Const of int
  | Add of expr * expr
  | Mult of expr * expr
  | VarPow of int


let rec mlist2 (xs : int list) (pow : int) : expr =
  match xs with
  | [] -> Const 0 (*dummy value*)
  | [x] -> mlist3 x pow
  | (x :: tt) -> let v =  mlist3 x pow
                 and v2 = mlist2 tt (pow+1) in   
                    Add(v,v2)
  and mlist3 (x : int) (pow : int) : expr =
    if pow < 1 then (Const x)
    else Mult(Const x, VarPow pow)
    
let mlist (xs : int list) : expr = mlist2 xs 0 


(*
let rec mlist2 (xs : int list) (pow : int) : expr option =
  match xs with
  | [] -> None
  | [x] -> Some (mlist3 x pow)
  | (x :: tt) -> let v =  mlist3 x pow
                 and v2 = mlist2 tt (pow+1) in   
                    match v2 with
		    | Some v3 -> Some (Add(v,v3))
		    | _ -> None
  and mlist3 (x : int) (pow : int) : expr =
    if pow < 1 then (Const x)
    else Mult(Const x, VarPow pow)
    
let mlist (xs : int list) : expr option = mlist2 xs 0 
  *)

(*
Define a function 

coeffs :: exp ⇒ int list 

that transforms an expression into a polynomial. 
  This may require auxiliary functions.
  Prove that coeffs preserves the value of the expression:
  
evalp (coeffs e) x = eval e x.

  Hint: consider the hint in Exercise 2.10.

  coeffs Var -> [0,1,0,0,0,0,0] ???
  coeffs Const a -> [a,0,0,0,0,0,0] ??? 
  coeffs 



(* this is going to be painful *)  
let rec coeffs2 (e : expr) : int list  =
  match e with
  | Var -> []
  | Const a -> []
  | Add  (e1,e2)  -> (coeffsh e1) :: (coeffs2 e2)
  | Mult (e1,e2)  -> []
and coeffsh (e : expr) : int =
  match e with
  | Var -> 1 (* not used ?*)
  | Const a -> a   
  | Mult (e1,e2)  -> (coeffsh e1) * (coeffsh e2)
  | Add (e1,e2)  -> 1 (* not used ? *)
and coeffs (e : expr) : int list = List.rev (coeffs2 e)


(* list of ints -> build expression e -> list ints == coefficients of e ?? *)
let ev5 = let v = [] in let e = evalph v in v = coeffs e
let ev6 = let v = [0] in let e = evalph v  in v = coeffs e
let ev7 = let v = [0;1] in let e = evalph v  in v = coeffs e
let ev8 = let v = [1;0] in let e = evalph v  in v = coeffs e
let ev9 = let v = [0;0;0] in let e = evalph v in v = coeffs e
let ev10 = let v = [-1] in let e = evalph v in (e,v,v = coeffs e)
let ev11 = let v = [-1;-2;-3;-4] in let e = evalph v in v = coeffs e
  *)












  
  



  




  
  

  
