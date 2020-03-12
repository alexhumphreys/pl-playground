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

-- maybe (VVar x) id (fromJust $ lookup x env)

partial
eval : Env -> Tm -> Val
eval env (Var x) = let findX = lookup x env in
                       (case findX of
                             Nothing => VVar x
                             (Just x') => (case x' of
                                                Nothing => VVar x
                                                (Just x'') => x''))
eval env (App t u) = case (eval env t, eval env u) of
                          (VLam _ t', u') => t' u'
                          (t', u') => VApp t' u'
eval env (Lam x t) = VLam x (\u => eval ((x, Just u) :: env) t)
eval env (Pi x a b) = VPi x (eval env a) (\u => eval ((x, Just u) :: env) b)
eval env (Let x _ t u) = eval ((x, Just (eval env t)) :: env) u
eval env U = VU
eval env (SrcPos _ t) = eval env t

partial
quote : Env -> Val -> Tm
quote env (VVar x) = Var x
quote env (VApp t u) = App (quote env t) (quote env u)
quote env VU = U
quote env (VPi x a b) = let freshX = fresh env x in
                            Pi x (quote env a) (quote ((x, Nothing) :: env) (b (VVar x)))
quote env (VLam x t) = let freshX = fresh env x in
                           Lam x (quote ((x, Nothing) :: env) (t (VVar x)))

partial
nf : Env -> Tm -> Tm
nf env = quote env . eval env

partial
nf0 : Tm -> Tm
nf0 = nf []

conv : Env -> Val -> Val -> Bool
