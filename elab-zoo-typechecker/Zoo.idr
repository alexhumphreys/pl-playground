module Zoo

data SourcePos = SP String Nat Nat

Name : Type
Name = String

mutual
  Ty : Type
  Ty = Tm

  RRaw : Type
  RRaw = Tm

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

partial
conv : Env -> Val -> Val -> Bool
conv env t u =
  case (t, u) of
       (VU, VU) => True
       (VPi x a b, VPi x' a' b') =>
         let gx = fresh env x in
         conv env a a' && conv ((gx, Nothing) :: env) (b (VVar gx)) (b' (VVar gx))
       (VLam x t, VLam x' t') =>
         let gx = fresh env x in
         conv ((gx, Nothing) :: env) (t (VVar gx)) (t' (VVar gx))

       -- checking eta conversion for Lam
       (VLam x t, u) =>
         let gx = fresh env x in
         conv ((gx, Nothing) :: env) (t (VVar gx)) (VApp u (VVar gx))
       (u, VLam x t) =>
         let gx = fresh env x in
         conv ((gx, Nothing) :: env) (VApp u (VVar gx)) (t (VVar gx))

       (VVar x, VVar x') => x == x'
       (VApp t u, VApp t' u') => conv env t t' && conv env u u'
       _ => False

VTy : Type
VTy = Val

Cxt : Type
Cxt = List (Name, VTy)

M : Type -> Type
M = Either (String, Maybe SourcePos)

report : String -> M a
report str = Left (str, Nothing)

quoteShow : Env -> Val -> String

addPos : SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) => Left (msg, Just pos)
  x => x

mutual
  partial
  infer : Env -> Cxt -> RRaw -> M VTy
  infer env cxt (Var x) =
    case lookup x cxt of
         Nothing => report $ "Name not in scope: " ++ x
         Just a  => Right a
  infer env cxt (Lam _ _) = report "Can't infer type for lambda expresion"
  infer env cxt (App t u) =
    do tty <- infer env cxt t
       ?infer_rhs_3
  infer env cxt U = Right VU
  infer env cxt (Pi x a b) =
    do Zoo.check env cxt a VU
       check ((x, Nothing) :: env) ((x, eval env a) :: cxt) b VU
       Right VU
  infer env cxt (Let x a t u) =
    let a' = eval env a in -- TODO not sure about
    do check env cxt a VU
       check env cxt t a'
       infer ((x, Just (eval env t)) :: env) ((x, a') :: cxt) u
  infer env cxt (SrcPos pos t) = addPos pos (infer env cxt t)

  partial
  check : Env -> Cxt -> RRaw -> VTy -> M ()
  check env cxt t a =
    case (t, a) of
         (SrcPos pos t', _) => addPos pos (check env cxt t' a)
         (Lam x t, VPi x' a b) =>
           let freshX' = fresh env x' in
           check ((x, Just (VVar freshX')) :: env) ((x, a) :: cxt) t (b (VVar x'))
         (Let x a' t' u, _) => -- TODO not sure about this one
           let a'' = eval env a' in
           do
             check env cxt a' VU
             check env cxt t' a''
             check ((x, Just (eval env t')) :: env) ((x, a'') :: cxt) u a
         _ => do
           tty <- infer env cxt t
           when (not (conv env tty a)) $
             -- (quoteShow env a) (quoteShow env tty))
             report ("type mismatch\n\nexpected type:\n\n  " ++ "" ++ "\n\ninferred type:\n\n " ++ "" ++ "\n")

