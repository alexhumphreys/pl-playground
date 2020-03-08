data Expr
  = Tr
  | Fl
  | IsZero Expr
  | Succ Expr
  | Pred Expr
  | If Expr Expr Expr
  | Zero

data TType
  = TBool
  | TNat
  | TArr TType TType

Eq TType where
  (==) TBool TBool = True
  (==) TNat TNat = True
  (==) (TArr x z) (TArr y w) = ((x == y) && (z ==w))
  (==) _ _ = False

isNum : Expr -> Bool
isNum Zero     = True
isNum (Succ t) = isNum t
isNum _        = False

isVal : Expr -> Bool
isVal Tr = True
isVal Fl = True
isVal Zero = True
isVal (Succ t) = isVal t
isVal _ = False

partial
eval1 : Expr -> Maybe Expr
eval1 t =
  case t of
       Succ t          => Succ <$> (eval1 t)
       Pred Zero       => Just Zero
       Pred (Succ t)   => case isNum t of
                               False => Nothing
                               True => Just t
       Pred t          => Pred <$> (eval1 t)
       IsZero Zero     => Just Tr
       IsZero (Succ t) => case isNum t of
                               False => Nothing -- might be wrong
                               True => Just Fl
       IsZero t        => IsZero <$> (eval1 t)
       If Tr  c _      => Just c
       If Fl _ a       => Just a
       If t c a        => (\t' => If t' c a) <$> eval1 t
       _               => Nothing

partial
nf : Expr -> Expr
nf t = fromMaybe t (nf <$> eval1 t)

partial
eval : Expr -> Maybe Expr
eval t = case (isVal t) of
              False => Just (nf t)
              True => Nothing

data TypeError
  = TypeMismatch TType TType

check : Expr -> Either TypeError TType

typeof : Expr -> Either TypeError TType
typeof t =
  case t of
       (IsZero a) => do
         ta <- typeof a
         case ta of
              TNat => Right TNat
              _ => Left (TypeMismatch ta TNat)
       (Succ a) => do
         ta <- typeof a
         case ta of
              TNat => Right TNat
              _ => Left (TypeMismatch ta TNat)
       (Pred a) => do
         ta <- typeof a
         case ta of
              TNat => Right TNat
              _ => Left (TypeMismatch ta TNat)
       (If a b c) => do
         ta <- typeof a
         tb <- typeof b
         tc <- typeof c
         case ta of
              TBool => case tb == tc of
                            True => Right tc
                            False => Left (TypeMismatch tb tc)
              _ => Left (TypeMismatch ta TBool)
       Zero => Right TNat
       Tr => Right TBool
       Fl => Right TBool
