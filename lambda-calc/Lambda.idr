import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

Name : Type
Name = String

showParen : String -> String
showParen x = "(" ++ x ++ ")"

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | Let Name Tm Tm     -- let x = t in u
Show Tm where
  show (Var str) = str
  show (Lam x t) = showParen ("λ" ++ x ++ "." ++ show t)
  show (App t u) = showParen ("" ++ show t ++ " " ++ show u)
  show (Let str tm1 tm2) = showParen ("Let " ++ str ++ " = " ++ show tm1 ++ " in " ++ show tm2)

-- parsing

keyword : String -> Bool
keyword x = x == "λ" || x == "in" || x == "let"

pIdent' : Parser Name
pIdent' = do f <- satisfy (isAlphaNum)
             i <- many (satisfy isAlphaNum)
             pure (pack (f :: i)) <* spaces

pIdent : Parser Name
pIdent = do
  str <- pIdent'
  guard (not (keyword str))
  pure str

pBind : Parser Name
pBind = pIdent <|> (token "_" *> pure "_")

mutual
  pAtom : Parser Tm
  pAtom = (Var <$> pIdent) <|> parens pTm -- what's `<$>` doing here?

  pTm : Parser Tm
  pTm = pLet <|>| pLam <|>| pSpine

  pLam : Parser Tm
  pLam = do
    char 'λ' <|> char '\\'
    xs <- some pBind
    token "."
    t <- pTm
    pure (foldr Lam t xs)

  pLet : Parser Tm
  pLet = do
    token "let"
    x <- pBind
    token "="
    t <- pTm
    token "in"
    u <- pTm
    pure $ Let x t u

  pSpine : Parser Tm
  pSpine = foldl1 App <$> some pAtom

-- evaluation

data Val
  = VVar Name
  | VApp Val Val
  | VLam Name (Val -> Val)

Env : Type
Env = List (Name, Maybe Val)

fresh : Env -> Name -> Name
fresh env "_" = "_"
fresh env x = case lookup x env of
                   Nothing => x
                   (Just _) => fresh env (x ++ "'")

eval : Env -> Tm -> Val
eval env (Var x) = let findX = lookup x env in
                       (case findX of
                             Nothing => VVar x
                             (Just x') => (case x' of
                                                Nothing => VVar x
                                                (Just x'') => x''))
eval env (App t u) = let evalT = eval env t
                         evalU = eval env u
                         in
                         (case evalT of
                               (VLam _ f) => f evalU
                               _ => VApp evalT evalU)
eval env (Lam x t) = VLam x (\u => eval ((x, Just u)::env) t)
eval env (Let x t u) = let nextEnv = Just (eval env t) in
                           eval ((x, nextEnv)::env) u

quote : Env -> Val -> Tm
quote env (VVar x) = Var x
quote env (VApp t u) = App (quote env t) (quote env u)
quote env (VLam x t) = let freshX = fresh env x in
                           Lam freshX (quote ((x, Nothing)::env) (t (VVar x)))
nf : Env -> Tm -> Tm
nf env = let qe = quote env
             ee = eval env in
             qe . ee

test : Maybe Tm
test = let parsed = (Lightyear.Strings.parse (pTm) "let five = \\s z. s (s (s (s (s z)))) in let add = \\a b s z. a s (b s z) in let mul = \\a b s z. a (b s) z in let ten = add five five in let hundred = mul ten ten in let thousand = mul ten hundred in let tenthousand = mul ten thousand in tenthousand") in
           (case parsed of
                 (Left l) => Nothing
                 (Right r) => Just (nf [] r))
