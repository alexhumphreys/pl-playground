-- expressions

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

aEquivHelper _ _ _ _ _ = False

mutual
  data Neutral
    = NVar Name
    | NApp Neutral Neutral
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
