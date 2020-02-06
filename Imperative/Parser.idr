module Imperative.Parser

import DataStructures as DS
import Lexer
import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Char
import Lightyear.Strings

identifier : Parser DS.AExpr
identifier = do f <- satisfy (isAlpha)
                i <- many letter
                pure (Var (pack (f :: i)))

intConst : Parser DS.AExpr
intConst = do i <- integer
              pure (IntConst i)

-- TODO come back for parens aExpression
aTerm : Parser DS.AExpr
aTerm = intConst <|> identifier

infixOp : Parser () -> (AExpr -> AExpr -> AExpr) -> Parser (AExpr -> AExpr -> AExpr)
infixOp l ctor = do
  _ <- l
  pure ctor

addOp : Parser (AExpr -> AExpr -> AExpr)
addOp = infixOp (rPlus) (ABinary Add) <|> infixOp (rMinus) (ABinary Subtract)
mulOp : Parser (AExpr -> AExpr -> AExpr)
mulOp = infixOp (rTimes) (ABinary Multiply) <|> infixOp (rDivide) (ABinary Divide)

mutual
  expression : Parser AExpr
  expression = chainl1 term addOp

  term : Parser DS.AExpr
  term = chainl1 factor mulOp

  factor : Parser DS.AExpr
  factor = intConst
    <|> identifier
    <|> negate
    <|> subExpr

  negate : Parser DS.AExpr
  negate = do (token "-")
              f <- factor
              pure $ Neg f

  subExpr : Parser DS.AExpr
  subExpr = do
    _ <- token "("
    expr <- expression
    _ <- token ")"
    pure expr
