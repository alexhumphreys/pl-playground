import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

Name : Type
Name = String

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | Let Name Tm Tm     -- let x = t in u

-- parsing

pIdent : Parser Name
pIdent = do f <- satisfy (isAlphaNum)
            i <- many (satisfy isAlphaNum)
            pure (pack (f :: i)) <* spaces

pBind : Parser Name
pBind = pIdent <|> (token "_" *> pure "_")

mutual
  pAtom : Parser Tm

  pTm : Parser Tm
  pTm  = pLam <|> pLet <|> pSpine

  pLam : Parser Tm
  pLam = do
    char '\\'
    x <- pBind
    token "="
    t <- pTm
    token "in"
    u <- pTm
    pure $ Let x t u

  pLet : Parser Tm

  pSpine : Parser Tm
