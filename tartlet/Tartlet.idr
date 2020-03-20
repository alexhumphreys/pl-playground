-- expressions

data SourcePos = SP String Nat Nat
Show SourcePos where
  show (SP x k j) = x ++ ":" ++ (show k) ++ "," ++ (show j)

data Name = Name' String

Show Name where
  show (Name' x) = x

Eq Name where
  (==) (Name' x) (Name' y) = x == y

data Expr
  = Var Name   -- x
  | Pi Name Expr Expr -- (Π ((x A)) B)
  | Lambda Name Expr -- (λ (x) b)
  | App Expr Expr -- (rator rand)
  | Sigma Name Expr Expr -- (Σ ((x A)) D)
  | Cons Expr Expr -- (cons a d)
  | Car Expr -- (car e)
  | Cdr Expr -- (cdr e)
  | Nat -- Nat
  | Zero -- zero
  | Add1 Expr -- (add1 e)
  | IndNat Expr Expr Expr Expr -- (ind-nat tgt mot base step)
  | Equal Expr Expr Expr -- (= A from to)
  | Same -- Same
  | Replace Expr Expr Expr -- (replace tgt mot base)
  | Trivial -- Trivial
  | Sole -- sole
  | Absurd -- Absurd
  | IndAbsurd Expr Expr -- (ind-Absurd tgt mot)
  | Atom -- Atom
  | Tick String -- 'a
  | U -- U
  | The Expr Expr -- (the t e)
  | SrcPos SourcePos Expr

Show Expr where
Eq Expr where

Namespace : Type
Namespace = List (Name, Integer)
%name Namespace ns1, ns2, ns3

-- alpha equivalence
aEquiv : Expr -> Expr -> Bool

aEquivHelper : (i : Integer) ->
               Namespace -> Expr ->
               Namespace -> Expr ->
               Bool
aEquivHelper i ns1 (Var x) ns2 (Var y) =
  case (lookup x ns1, lookup y ns2) of
       (Nothing, Nothing) => x == y
       (Just j, Just k) => i == j
       _ => False

aEquivHelper i ns1 (Pi x a1 r1) ns2 (Pi y a2 r2) =
  aEquivHelper i ns1 a1 ns2 a2 &&
  aEquivHelper (i+1) ((x, i) :: ns1) r1 ((y, i) :: ns2) r2

aEquivHelper i ns1 (Lambda x body1) ns2 (Lambda y body2) =
  aEquivHelper (i+1) ((x, i) :: ns1) body1 ((y, i) :: ns2) body2

aEquivHelper i ns1 (App rator1 rand1) ns2 (App rator2 rand2) =
  aEquivHelper i ns1 rator1 ns2 rator2 &&
  aEquivHelper i ns1 rand1 ns2 rand2

aEquivHelper i ns1 (Sigma x a1 d1) ns2 (Sigma y a2 d2) =
  aEquivHelper i ns1 a1 ns2 a2 &&
  aEquivHelper (i+1) ((x, i) :: ns1) d1 ((y, i) :: ns2) d2

aEquivHelper i ns1 (Cons car1 cdr1) ns2 (Cons car2 cdr2) =
  aEquivHelper i ns1 car1 ns2 car2 &&
  aEquivHelper i ns1 cdr1 ns2 cdr2

aEquivHelper i ns1 (Car pair1) ns2 (Car pair2) =
  aEquivHelper i ns1 pair1 ns2 pair2
aEquivHelper i ns1 (Cdr pair1) ns2 (Cdr pair2) =
  aEquivHelper i ns1 pair1 ns2 pair2

aEquivHelper _ _ Nat _ Nat = True
aEquivHelper _ _ Zero _ Zero = True

aEquivHelper i ns1 (Add1 e1) ns2 (Add1 e2) =
  aEquivHelper i ns1 e1 ns2 e2

aEquivHelper i ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2 &&
  aEquivHelper i ns1 mot1 ns2 mot2 &&
  aEquivHelper i ns1 base1 ns2 base2 &&
  aEquivHelper i ns1 step1 ns2 step2

aEquivHelper i ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
  aEquivHelper i ns1 ty1 ns2 ty2 &&
  aEquivHelper i ns1 from1 ns2 from2 &&
  aEquivHelper i ns1 to1 ns2 to2

aEquivHelper _ _ Same _ Same = True

aEquivHelper i ns1 (Replace tgt1 mot1 base1) ns2 (Replace tgt2 mot2 base2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2 &&
  aEquivHelper i ns1 mot1 ns2 mot2 &&
  aEquivHelper i ns1 base1 ns2 base2

aEquivHelper _ _ Trivial _ Trivial = True
aEquivHelper _ _ Sole _ Sole = True
aEquivHelper _ _ Absurd _ Absurd = True
aEquivHelper _ _ Atom _ Atom = True
aEquivHelper _ _ U _ Atom = True

aEquivHelper i ns1 (IndAbsurd tgt1 mot1) ns2 (IndAbsurd tgt2 mot2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2 &&
  aEquivHelper i ns1 mot1 ns2 mot2

aEquivHelper i ns1 (Tick a1) ns2 (Tick a2) = a1 == a2

aEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True
aEquivHelper i ns1 (The t1 e1) ns2 (The t2 e2) =
  aEquivHelper i ns1 t1 ns2 t2 &&
  aEquivHelper i ns1 e1 ns2 e2

aEquivHelper i ns1 (SrcPos str1 e1) ns2 (SrcPos str2 e2) =
  aEquivHelper i ns1 e1 ns2 e2

aEquivHelper _ _ _ _ _ = False

mutual
  data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NCar Neutral
    | NCdr Neutral
    | NIndNat Neutral Normal Normal Normal
    | NReplace Neutral Normal Normal
    | NIndAbsurd Neutral Normal

  data Normal = Normal' Ty Value

  Env : Type -- Now a type alias
  Env = List (Name,Value)
  %name Env env, env1, env2

  record Closure where
    constructor MkClosure
    closureEnv : Env
    closureName : Name
    closureBody : Expr

  Ty : Type
  Ty = Value

  -- Values
  data Value
    = VPi Ty Closure
    | VLambda Closure
    | VSimga Ty Closure
    | VPair Value Value
    | VNat
    | VZero
    | VAdd1 Value
    | VEq Ty Value Value
    | VSame
    | VTrivial
    | VSole
    | VAbsurd
    | VAtom
    | VTick String
    | VU
    | VNeutral Ty Neutral

extendEnv : Env -> Name -> Value -> Env
extendEnv env x v = ((x, v) :: env)

evalVar : Env -> Name -> Maybe Value
evalVar [] x = Nothing
evalVar ((y, v) :: env) x = case x == y of
                                  True => Just v
                                  False => evalVar env x

-- definitions and dependent types
data CtxEntry = Def Ty Value | IsA Ty

Ctx : Type
Ctx = List (Name, CtxEntry)
%name Ctx ctx, ctx1, ctx2

initCtx : Ctx
initCtx = []

ctxNames : Ctx -> List Name
ctxNames ctx = map fst ctx

extendCtx : Ctx -> Name -> Ty -> Ctx
extendCtx ctx x t = (x, (IsA t)) :: ctx

define : Ctx -> Name -> Ty -> Value -> Ctx
define ctx x t v = (x, Def t v) :: ctx

lookupType : Ctx -> Name -> Either String Ty -- didn't use message type
lookupType [] x = Left "unbound variable: " -- TODO ++ show x
lookupType ((y, e) :: ctx) x =
  (case x == y of
        False => lookupType ctx x
        True => (case e of
                      (Def t _) => Right t
                      (IsA t) => Right t))

mkEnv : Ctx -> Env
mkEnv [] = []
mkEnv ((x, e) :: ctx) =
  let env = mkEnv ctx in
  (case e of
        (Def _ v) => (x, v) :: env
        (IsA t) => let v = VNeutral t (NVar x) in
                       (x, v) :: env)

-- evaluator
mutual
  partial
  evalClosure : Closure -> Value -> Value
  evalClosure (MkClosure env x e) v =
    eval (extendEnv env x v) e

  partial
  eval : Env -> Expr -> Value
  eval env (Var x) = ?eval_rhs_1
  eval env (Pi x dom ran) = VPi (eval env dom) (MkClosure env x ran)
  eval env (Lambda x body) = VLambda (MkClosure env x body)
  eval env (App rator rand) = doApply (eval env rator) (eval env rand)
  eval env (Sigma x carType cdrType) = VSimga (eval env carType) (MkClosure env x cdrType)
  eval env (Cons a d) = VPair (eval env a) (eval env d)
  eval env (Car e) = doCar (eval env e)
  eval env (Cdr e) = doCdr (eval env e)
  eval env Nat = VNat
  eval env Zero = VZero
  eval env (Add1 e) = VAdd1 (eval env e)
  eval env (IndNat tgt mot base step) =
    doIndNat (eval env tgt) (eval env mot) (eval env base) (eval env step)
  eval env (Equal ty from to) =
    VEq (eval env ty) (eval env from) (eval env to)
  eval env Same = VSame
  eval env (Replace tgt mot base) =
    doReplace (eval env tgt) (eval env mot) (eval env base)
  eval env Trivial = VTrivial
  eval env Sole = VSole
  eval env Absurd = VAbsurd
  eval env (IndAbsurd tgt mot) =
    doIndAbsurd (eval env tgt) (eval env mot)
  eval env Atom = VAtom
  eval env (Tick x) = VTick x
  eval env U = VU
  eval env (The ty e) = eval env e
  eval env (SrcPos _ e) = eval env e

  -- eliminators
  partial
  doCar : Value -> Value
  doCar (VPair v1 v2) = v1
  doCar (VNeutral (VSimga aT dT) neu) =
    VNeutral aT (NCar neu)

  partial
  doCdr : Value -> Value
  doCdr v = case v of
                 (VPair v1 v2) => v2
                 (VNeutral (VSimga aT dT) neu) =>
                   VNeutral (evalClosure dT (doCar v)) (NCdr neu)

  partial
  doApply : Value -> Value -> Value
  doApply (VLambda closure) arg =
    evalClosure closure arg
  doApply (VNeutral (VPi dom ran) neu) arg =
    VNeutral (evalClosure ran arg) (NApp neu (Normal' dom arg))

  partial
  doIndAbsurd : Value -> Value -> Value
  doIndAbsurd (VNeutral VAbsurd neu) mot =
    VNeutral mot (NIndAbsurd neu (Normal' VU mot))

  partial
  doReplace : Value -> Value -> Value -> Value
  doReplace VSame mot base =
    base
  doReplace (VNeutral (VEq ty from to) neu) mot base =
    VNeutral (doApply mot to)
      (NReplace neu (Normal' motT mot) (Normal' baseT base))
    where
      motT = VPi ty (MkClosure ([]) (Name' "x") U)
      baseT = doApply mot from

  partial
  indNatStepType : Value -> Value
  indNatStepType mot =
    eval [(Name' "mot", mot)]
      (Pi (Name' "n-1") Nat
        (Pi (Name' "almost") (App (Var (Name' "mot")) (Var (Name' "n-1")))
          (App (Var (Name' "mot"))
            (Add1 (Var (Name' "n-1"))))))

  partial
  doIndNat : Value -> Value -> Value -> Value -> Value
  doIndNat VZero mot base step =
    base
  doIndNat (VAdd1 v) mot base step =
    doApply (doApply step v) (doIndNat v mot base step)
  doIndNat tgt@(VNeutral VNat neu) mot base step =
    VNeutral (doApply mot tgt) (NIndNat neu
      (Normal' (VPi VNat (MkClosure [] (Name' "k") U)) mot) (Normal' (doApply mot VZero) base)
        (Normal' (indNatStepType mot) step))
