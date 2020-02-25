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