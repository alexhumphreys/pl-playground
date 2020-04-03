-- expressions

data SourcePos = SP String Nat Nat
Show SourcePos where
  show (SP x k j) = x ++ ":" ++ (show k) ++ "," ++ (show j)

one : Nat
one = unsafePerformIO $ do putStrLn "ALEX"
                           pure 3

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

aEquiv : Expr -> Expr -> Bool
aEquiv e1 e2 = aEquivHelper 0 [] e1 [] e2

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
    | VSigma Ty Closure
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
  data Error
    = MissingValue String
    | CarError
    | CdrError
    | ApplyError
    | IndAbsurdError
    | DoReplaceError
    | DoIndNatError
    | ReadBackTypedError
    | ErrorMessage String

  partial
  evalClosure : Closure -> Value -> Either Error Value
  evalClosure (MkClosure env x e) v =
    eval (extendEnv env x v) e

  evalVar : Env -> Name -> Either Error Value
  evalVar [] x = Left (MissingValue (show x ++ " not found in env"))
  evalVar ((y, v) :: env) x = case x == y of
                                    True => Right v
                                    False => evalVar env x

  partial
  eval : Env -> Expr -> Either Error Value
  eval env (Var x) = evalVar env x
  eval env (Pi x dom ran) =
    do dom' <- eval env dom
       Right (VPi dom' (MkClosure env x ran))
  eval env (Lambda x body) = Right (VLambda (MkClosure env x body))
  eval env (App rator rand) =
    do rator' <- eval env rator
       rand' <- eval env rand
       doApply rator' rand'
  eval env (Sigma x carType cdrType) =
    do carType' <- eval env carType
       Right (VSigma carType' (MkClosure env x cdrType))
  eval env (Cons a d) =
    do a' <- eval env a
       d' <- eval env d
       Right (VPair a' d')
  eval env (Car e) =
    do e' <- eval env e
       doCar e'
  eval env (Cdr e) =
    do e' <- eval env e
       doCdr e'
  eval env Nat = Right VNat
  eval env Zero = Right VZero
  eval env (Add1 e) =
    do e' <- eval env e
       Right (VAdd1 e')
  eval env (IndNat tgt mot base step) =
    do tgt' <- eval env tgt
       mot' <- eval env mot
       base' <- eval env base
       step' <- eval env step
       doIndNat tgt' mot' base' step'
  eval env (Equal ty from to) =
    do ty' <- eval env ty
       from' <- eval env from
       to' <- eval env to
       Right (VEq ty' from' to')
  eval env Same = Right VSame
  eval env (Replace tgt mot base) =
    do tgt' <- eval env tgt
       mot' <- eval env mot
       base' <- eval env base
       doReplace tgt' mot' base'
  eval env Trivial = Right VTrivial
  eval env Sole = Right VSole
  eval env Absurd = Right VAbsurd
  eval env (IndAbsurd tgt mot) =
    do tgt' <- eval env tgt
       mot' <- eval env mot
       doIndAbsurd tgt' mot'
  eval env Atom = Right VAtom
  eval env (Tick x) = Right (VTick x)
  eval env U = Right VU
  eval env (The ty e) = eval env e
  eval env (SrcPos _ e) = eval env e

  -- eliminators
  doCar : Value -> Either Error Value
  doCar (VPair v1 v2) = Right v1
  doCar (VNeutral (VSigma aT dT) neu) =
    Right (VNeutral aT (NCar neu))
  doCar _ = Left CarError

  partial
  doCdr : Value -> Either Error Value
  doCdr (VPair v1 v2) = Right v2
  doCdr v@(VNeutral (VSigma aT dT) neu) =
    do v' <- doCar v
       cl' <- evalClosure dT v'
       Right (VNeutral cl' (NCdr neu))
  doCdr _ = Left CdrError

  partial
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda closure) arg =
    evalClosure closure arg
  doApply (VNeutral (VPi dom ran) neu) arg =
    do arg' <- evalClosure ran arg
       Right (VNeutral arg' (NApp neu (Normal' dom arg)))
  doApply _ _ = Left ApplyError

  doIndAbsurd : Value -> Value -> Either Error Value
  doIndAbsurd (VNeutral VAbsurd neu) mot =
    Right (VNeutral mot (NIndAbsurd neu (Normal' VU mot)))
  doIndAbsurd _ _ = Left IndAbsurdError

  partial
  doReplace : Value -> Value -> Value -> Either Error Value
  doReplace VSame mot base =
    Right base
  doReplace (VNeutral (VEq ty from to) neu) mot base =
    do v' <- doApply mot to
       baseT' <- doApply mot from
       Right (VNeutral v'
         (NReplace neu (Normal' motT mot) (Normal' baseT' base)))
    where
      motT = VPi ty (MkClosure ([]) (Name' "x") U)
  doReplace _ _ _ = Left DoReplaceError

  partial
  indNatStepType : Value -> Either Error Value
  indNatStepType mot =
    eval [(Name' "mot", mot)]
      (Pi (Name' "n-1") Nat
        (Pi (Name' "almost") (App (Var (Name' "mot")) (Var (Name' "n-1")))
          (App (Var (Name' "mot"))
            (Add1 (Var (Name' "n-1"))))))

  partial
  doIndNat : Value -> Value -> Value -> Value -> Either Error Value
  doIndNat VZero mot base step =
    Right base
  doIndNat (VAdd1 v) mot base step =
    do rator' <- (doApply step v)
       rand' <- (doIndNat v mot base step)
       doApply rator' rand'
  doIndNat tgt@(VNeutral VNat neu) mot base step =
    do a' <- (doApply mot tgt)
       b' <- (doApply mot VZero)
       c' <- (indNatStepType mot)
       Right (VNeutral a' (NIndNat neu
         (Normal' (VPi VNat (MkClosure [] (Name' "k") U)) mot) (Normal' b' base)
           (Normal' c' step)))
  doIndNat _ _ _ _ = Left DoIndNatError

-- fresh names

nextName : Name -> Name
nextName (Name' x) = Name' ((show x) ++ "'")

-- could possibly fail for a list like [n', n'', n']
freshen : List Name -> Name -> Name
freshen [] n = n
freshen (x :: used) n = case x == n of
                             False => freshen used n
                             True => freshen used (nextName n)

-- reading back
mutual
  partial
  readBackNeutral : Ctx -> Neutral -> Either Error Expr
  readBackNeutral ctx (NVar x) = Right (Var x)
  readBackNeutral ctx (NApp neu arg) =
    do neu' <- readBackNeutral ctx neu
       arg' <- readBackNormal ctx arg
       Right (App neu' arg')
  readBackNeutral ctx (NCar neu) =
    do car <- readBackNeutral ctx neu
       Right (Car car)
  readBackNeutral ctx (NCdr neu) =
    do cdr <- readBackNeutral ctx neu
       Right (Cdr cdr)
  readBackNeutral ctx (NIndNat neu mot base step) =
    do neu' <- readBackNeutral ctx neu
       mot' <- readBackNormal ctx mot
       base' <- readBackNormal ctx base
       step' <- readBackNormal ctx step
       Right (IndNat neu' mot' base' step')
  readBackNeutral ctx (NReplace neu mot base) =
    do neu' <- readBackNeutral ctx neu
       mot' <- readBackNormal ctx mot
       base' <- readBackNormal ctx base
       Right (Replace neu' mot' base')
  readBackNeutral ctx (NIndAbsurd neu mot) =
    do neu' <- readBackNeutral ctx neu
       mot' <- readBackNormal ctx mot
       Right (IndAbsurd (The Absurd neu') mot')

  partial
  readBackTyped : Ctx -> Ty -> Value -> Either Error Expr
  readBackTyped ctx VNat VZero = Right Zero
  readBackTyped ctx VNat (VAdd1 v) =
    do n <- (readBackTyped ctx VNat v)
       Right (Add1 n)
  readBackTyped ctx (VPi dom ran) fun =
    let x = freshen (ctxNames ctx) (closureName ran)
        xVal = VNeutral dom (NVar x)
        ctx' = extendCtx ctx x dom in
    do ty' <- evalClosure ran xVal
       v' <- doApply fun xVal
       body <- readBackTyped ctx' ty' ty'
       Right (Lambda x body)
  readBackTyped ctx (VSigma aT dT) pair =
    do carVal <- doCar pair
       car <- readBackTyped ctx aT carVal
       cdrT <- evalClosure dT carVal
       cdrVal <- doCdr pair
       cdr <- readBackTyped ctx cdrT cdrVal
       Right (Cons car cdr)
  readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) =
    do a <- readBackNeutral ctx neu
       Right (The Absurd a)
  readBackTyped ctx (VEq _ _ _) VSame = Right Same
  readBackTyped ctx VAtom (VTick x) = Right (Tick x)
  readBackTyped ctx VU VNat = Right Nat
  readBackTyped ctx VU VAtom = Right Atom
  readBackTyped ctx VU VTrivial = Right Trivial
  readBackTyped ctx VU VAbsurd = Right Absurd
  readBackTyped ctx VU (VEq t from to) =
    do a <- readBackTyped ctx VU t
       b <- readBackTyped ctx t from
       c <- readBackTyped ctx t to
       Right (Equal a b c)
  readBackTyped ctx VU (VSigma aT dT) =
    let x = freshen (ctxNames ctx) (closureName dT) in
        do a <- readBackTyped ctx VU aT
           body <- evalClosure dT (VNeutral aT (NVar x))
           d <- readBackTyped (extendCtx ctx x aT) VU body
           Right (Sigma x a d)
  readBackTyped ctx VU (VPi aT bT) =
    let x = freshen (ctxNames ctx) (closureName bT) in
        do a <- readBackTyped ctx VU aT
           body <- evalClosure bT (VNeutral aT (NVar x))
           b <- readBackTyped (extendCtx ctx x aT) VU body
           Right (Pi x a b)
  readBackTyped ctx VU VU = Right U
  readBackTyped ctx t (VNeutral t' neu) = readBackNeutral ctx neu
  readBackTyped _ otherT otherE = Left ReadBackTypedError

  partial
  readBackNormal : Ctx -> Normal -> Either Error Expr
  readBackNormal ctx (Normal' t v) = readBackTyped ctx t v

-- helpers
lookupType : Ctx -> Name -> Either Error Ty -- didn't use message type
lookupType [] x = Left (ErrorMessage "unbound variable: ") -- TODO ++ show x
lookupType ((y, e) :: ctx) x =
  (case x == y of
        False => lookupType ctx x
        True => (case e of
                      (Def t _) => Right t
                      (IsA t) => Right t))

unexpected : Ctx -> String -> Value -> Either Error a

isPi : Ctx -> Value -> Either Error (Ty, Closure)
isPi _ (VPi a b) = Right (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isSigma : Ctx -> Value -> Either Error (Ty, Closure)
isSigma _ (VSigma a b) = Right (a, b)
isSigma ctx other = unexpected ctx "Not a Sigma type" other

isNat : Ctx -> Value -> Either Error ()
isNat _ VNat = Right ()
isNat ctx other = unexpected ctx "Not Nat" other

isEqual : Ctx -> Value -> Either Error (Ty, Value, Value)
isEqual _ (VEq ty from to) = Right (ty, from, to)
isEqual ctx other = unexpected ctx "Not an equality type" other

isAbsurd : Ctx -> Value -> Either Error ()
isAbsurd _ VAbsurd = Right ()
isAbsurd ctx other = unexpected ctx "Not Absurd: " other

isTrivial : Ctx -> Value -> Either Error ()
isTrivial _ VTrivial = Right ()
isTrivial ctx other = unexpected ctx "Not Trivial" other

isAtom : Ctx -> Value -> Either Error ()
isAtom _ VAtom = Right ()
isAtom ctx other = unexpected ctx "Not Atom" other

-- checking/synthesis
mutual
  partial
  check : Ctx -> Expr -> Ty -> Either Error ()
  check ctx (Lambda x body) t = ?check_rhs_3
  check ctx (Cons a d) t = ?check_rhs_6
  check ctx Zero t = isNat ctx t
  check ctx (Add1 n) t = do
    isNat ctx t
    check ctx n VNat
  check ctx Same t = do
    (t, from, to) <- isEqual ctx t
    convert ctx t from to
  check ctx Sole t = isTrivial ctx t
  check ctx (Tick x) t = isAtom ctx t
  check ctx other t = do
    t' <- synth ctx other
    convert ctx VU t' t

  convert : Ctx -> Ty -> Value -> Value -> Either Error ()

  partial
  synth : Ctx -> Expr -> Either Error Ty
  synth ctx (Var x) = lookupType ctx x
  synth ctx (Pi x a b) =
    do check ctx a VU
       v <- eval (mkEnv ctx) a
       check (extendCtx ctx x v) b VU
       Right VU
  synth ctx (App rator rand) =
    do funTy <- synth ctx rator
       (a, b) <- isPi ctx funTy
       check ctx rand a
       body <- eval (mkEnv ctx) rand
       evalClosure b body
  synth ctx (Sigma x a b)
    = do check ctx a VU
         a' <- eval (mkEnv ctx) a
         check (extendCtx ctx x a') b VU
         Right VU
  synth ctx (Car e) =
    do t <- synth ctx e
       (aT, dT) <- isSigma ctx t
       Right aT
  synth ctx (Cdr e) =
    do t <- synth ctx e
       (aT, dT) <- isSigma ctx t
       e' <- eval (mkEnv ctx) e
       body <- doCar e'
       evalClosure dT body
  synth ctx Nat = Right VU
  synth ctx (IndNat tgt mot base step)
    = do t <- synth ctx tgt
         tgtV <- eval (mkEnv ctx) tgt
         motTy <- eval (mkEnv []) (Pi (Name' "x") Nat U)
         check ctx mot motTy
         motV <- eval (mkEnv ctx) mot
         z' <- doApply motV VZero
         check ctx base z'
         m' <- indNatStepType motV
         check ctx step m'
         doApply motV tgtV
  synth ctx (Equal ty from to)
    = do check ctx ty VU
         tyV <- eval (mkEnv ctx) ty
         check ctx from tyV
         check ctx to tyV
         Right VU
  synth ctx (Replace tgt mot base)
    = do t <- synth ctx tgt
         (ty, from, to) <- isEqual ctx t
         motTy <- eval ([(Name' "ty", ty)]) (Pi (Name' "x") (Var (Name' "ty")) U)
         check ctx mot motTy
         motV <- eval (mkEnv ctx) mot
         fromV <- doApply motV from
         check ctx base fromV
         doApply motV to
  synth ctx Trivial = Right VU
  synth ctx Absurd = Right VU
  synth ctx (IndAbsurd tgt mot)
    = do t <- synth ctx tgt
         isAbsurd ctx t
         check ctx mot VU
         eval (mkEnv ctx) mot
  synth ctx Atom = Right VU
  synth ctx U = Right VU
  synth ctx (The ty expr)
    = do check ctx ty VU
         tyV <- eval (mkEnv ctx) ty
         check ctx expr tyV
         Right tyV
  synth ctx other = Left (ErrorMessage "Unable to synthesize a type for ") -- ++ show other
