


type expr =
  | Var         
  | Const of int
  | Add of expr * expr
  | Mult of expr * expr

let e1 = Var
let e2 = Const 3
let e3 = Add (Var,Var)

let rec eval (e : expr) (x : int) : int =
  match e with
  | Var -> x
  | Const i -> i
  | Add (e1, e2) -> (eval e1 x) + (eval e2 x)
  | Mult (e1, e2) -> (eval e1 x) * (eval e2 x)

let ev1 = eval e1 3
let ev2 = eval e2 3
let ev3 = eval e3 3



let rec simp (e : expr) =
  match e with
  | Var -> Var 
  | Const i -> Const i
  | Mult (Const a , Const b) -> Const (a * b)
  | Add  (Const a , Const b) -> Const (a + b)
  | Mult (Const 0 , b) -> Const 0
  | Mult (a , Const 0) -> Const 0
  | Mult (Const 1 , b) -> simp b
  | Mult (e1,e2) -> Mult (simp e1,simp e2)
  | Add (e1, e2) -> Add (simp e1 ,simp e2)
  
let rec keep_simp (e:expr) =
  let e1 = simp e in
  let e2 = simp e1 in
  if e1 = e2 then e2 else keep_simp e2
  


(*
  [4;2;-1;3] translates to 4 + 2x + -1x^2 + 3x^3 lets call this evalph 
  evalp simply passes to eval , offloads building expression to evalph
  *)

let rec evalph (xs : int list) (e : expr) (acc : expr)  =
  match xs with
  | [] -> acc
  | (h :: t) -> evalph t (Mult (e, Var)) (Add (Mult(Const h,e),acc))
  
let evalp (xs:int list) (x:int) : int =  eval (evalph xs (Const 1) (Const 0)) x

let ev4 = evalph [4;2;-1;3] (Const 1) (Const 0)

(* val ev4 : expr =
  Add (Mult (Const 3, Mult (Mult (Mult (Const 1, Var), Var), Var)),
   Add (Mult (Const (-1), Mult (Mult (Const 1, Var), Var)),
    Add (Mult (Const 2, Mult (Const 1, Var)),
   Add (Mult (Const 4, Const 1), Const 0))))

should we simplify it - if so how ?
   *)

let ev5 = simp ev4



  




  
  

  
