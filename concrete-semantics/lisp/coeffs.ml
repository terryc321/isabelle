
#use "mlist.ml";;

(** --- begin here --- **)

let rec coeffs (e : expr) : int list =
  match e with
  | Var -> []
  | Const n -> [n]  
  | Add (x,y) -> (coeffs x) @ (coeffs y)
  | Mult (x,y) -> (coeffs x) @ (coeffs y)
  | VarPow n -> []

