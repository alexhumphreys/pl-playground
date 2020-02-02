import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

data Expression
  = Numeral Integer
  | Plus Expression Expression
  | Minus Expression Expression
  | Times Expression Expression
  | Divide Expression Expression
  | Negate Expression

E : Type
E = Expression

mutual
  Show Expression where
    show (Numeral n) = "(Numeral " ++ (show n) ++ ")"
    show (Plus l r) = _show "Plus" l r
    show (Minus l r) = _show "Minus" l r
    show (Times l r) = _show "Times" l r
    show (Divide l r) = _show "Divide" l r
    show (Negate e) = "(Negate " ++ (show e) ++ ")"

  _show : String -> Expression -> Expression -> String
  _show x l r = "(" ++ x ++ " " ++ (show l) ++ " " ++ (show r) ++ ")"

numeral : Parser Expression
numeral = do i <- integer
             pure (Numeral i)

minus : Parser Char
minus = satisfy (== '-')

lparen : Parser Char
lparen = satisfy (== '(')

rparen : Parser Char
rparen = satisfy (== ')')

infixOp : Parser Char -> (E -> E -> E) -> Parser (E -> E -> E)
infixOp l ctor = do
  _ <- l
  pure ctor

addOp : Parser (Expression -> Expression -> Expression)
addOp = infixOp (char '+') Plus <|> infixOp (char '-') Minus

mulOp : Parser (Expression -> Expression -> Expression)
mulOp = infixOp (char '*') Times <|> infixOp (char '/') Times

mutual
  expression : Parser Expression
  expression = chainl1 term addOp

  term : Parser Expression
  term = chainl1 factor mulOp

  negate : Parser Expression
  negate = do
    _ <- minus
    f <- factor
    pure $ Negate f

  subExp : Parser Expression
  subExp = do
    _ <- lparen
    expr <- expression
    _ <- rparen
    pure expr

  factor : Parser Expression
  factor = numeral
       <|> subExp
       <|> negate
