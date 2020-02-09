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

infixOp : Parser () -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp l ctor = do
  _ <- l
  pure ctor

addOp : Parser (AExpr -> AExpr -> AExpr)
addOp = infixOp (rPlus) (ABinary Add) <|> infixOp (rMinus) (ABinary Subtract)
mulOp : Parser (AExpr -> AExpr -> AExpr)
mulOp = infixOp (rTimes) (ABinary Multiply) <|> infixOp (rDivide) (ABinary Divide)

mutual
  aExpression : Parser AExpr
  aExpression = chainl1 term addOp

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
    expr <- aExpression
    _ <- token ")"
    pure expr

-- relational
relationalOp : Parser (AExpr -> AExpr -> BExpr)
relationalOp = (rGT) *> pure (RBinary Greater) <|> (rLT) *> pure (RBinary Less)

rExpression : Parser BExpr
rExpression =
  do a1 <- aExpression
     op <- relationalOp
     a2 <- aExpression
     pure (op a1 a2)

-- come back for parens bExpression
mutual
  bTerm : Parser BExpr
  bTerm = rTrue *> pure (BoolConst True) <|> rFalse *> pure (BoolConst False) <|> rExpression

  boolOp : Parser (BExpr -> BExpr -> BExpr)
  boolOp = infixOp (rAnd) (BBinary And) <|> infixOp (rOr) (BBinary Or)

  notOp : Parser (BExpr)
  notOp = do rNot
             b <- bExpression
             pure (BNot b)

  bExpression : Parser BExpr
  bExpression = notOp <|> chainl1 bTerm boolOp
