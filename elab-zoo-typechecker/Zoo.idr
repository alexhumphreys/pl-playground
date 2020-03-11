data SourcePos = SP String Nat Nat

Name : Type
Name = String

mutual
  Ty : Type
  Ty = Tm

  Raw : Type
  Raw = Tm

  data Tm
    = Var Name
    | Lam Name Tm
    | App Tm Tm
    | U
    | Pi Name Ty Ty
    | Let Name Ty Tm Tm
    | SrcPos SourcePos Tm
%name Tm t, u

data Val
  = VVar Name
  | VApp Val Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

Env : Type
Env = List (Name, Maybe Val)
%name Env env, env1, env2, env3

fresh : Env -> Name -> Name
fresh env "_" = "_"
fresh [] x = x
fresh (y :: xs) x = case x == fst y of
                         False => fresh xs x
                         True => fresh xs (x ++ "'")
