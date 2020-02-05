module Imperative.Lexer

import DataStructures as DS
import Lexer
import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Char
import Lightyear.Strings

identifier : Parser DS.AExpr
identifier = do i <- many letter
                pure (Var (pack i))

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
