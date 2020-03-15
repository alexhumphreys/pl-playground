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

aEquivHelper i ns1 (IndNat x z w s) ns2 y = ?aEquivHelper_rhs_12
aEquivHelper i ns1 (Equal x z w) ns2 y = ?aEquivHelper_rhs_13
aEquivHelper i ns1 Same ns2 y = ?aEquivHelper_rhs_14
aEquivHelper i ns1 (Replace x z w) ns2 y = ?aEquivHelper_rhs_15
aEquivHelper i ns1 Trivial ns2 y = ?aEquivHelper_rhs_16
aEquivHelper i ns1 Sole ns2 y = ?aEquivHelper_rhs_17
aEquivHelper i ns1 Absurd ns2 y = ?aEquivHelper_rhs_18
aEquivHelper i ns1 (IndAbsurd x z) ns2 y = ?aEquivHelper_rhs_19
aEquivHelper i ns1 Atom ns2 y = ?aEquivHelper_rhs_20
aEquivHelper i ns1 (Tick x) ns2 y = ?aEquivHelper_rhs_21
aEquivHelper i ns1 U ns2 y = ?aEquivHelper_rhs_22
aEquivHelper i ns1 (The x z) ns2 y = ?aEquivHelper_rhs_23
aEquivHelper _ _ _ _ _ = False
