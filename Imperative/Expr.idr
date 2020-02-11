import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

data Assoc = AssocNone
           | AssocLeft
           | AssocRight

{-
BinaryOpParser : Type
BinaryOpParser = (Parser () -> (Type -> Type -> Type) -> Parser (Type -> Type -> Type))

UnaryOpParser : Type
UnaryOpParser = (Parser () -> (Type -> Type) -> Parser (Type -> Type))
-}

-- Parser () -> (a -> a -> a) -> Parser (a -> a -> a)
data Operator = Infix (Parser () -> (a -> a -> a) -> Parser (a -> a -> a)) Assoc
              | Prefix (Parser () -> (a -> a) -> Parser (a -> a))
              | Postfix (Parser () -> (a -> a) -> Parser (a -> a))

LO : Type
LO = List Operator

OperatorTable : Type
OperatorTable = List LO

record Associations where
       constructor MkAssociations
       rassoc : List g
       lassoc : List g
       nassoc : List g
       prefixx : List g
       postfix : List g

ACC : Type
ACC = (LO,LO,LO,LO,LO)

buildExpressionParser : OperatorTable -> Parser f -> Parser f
buildExpressionParser operators simpleExpr =
  ?bar
  where
    makeParser : Parser ctor -> List Operator -> ctor
    makeParser term ops = ?foo
                        -- (rassoc,lassoc,nassoc,prefix,postfix)
    splitOp : Operator -> Associations -> Associations
    splitOp (Infix op AssocNone) (MkAssociations rassoc lassoc nassoc prefixx postfix) = MkAssociations rassoc lassoc (nassoc) prefixx postfix
    splitOp (Infix op AssocLeft) (MkAssociations rassoc lassoc nassoc prefixx postfix) = MkAssociations rassoc lassoc nassoc prefixx postfix
    splitOp (Infix op AssocRight) (MkAssociations rassoc lassoc nassoc prefixx postfix) = MkAssociations rassoc lassoc nassoc prefixx postfix
    splitOp (Prefix op) (MkAssociations rassoc lassoc nassoc prefixx postfix) = MkAssociations rassoc lassoc nassoc prefixx postfix
    splitOp (Postfix op) (MkAssociations rassoc lassoc nassoc prefixx postfix) = MkAssociations rassoc lassoc nassoc prefixx postfix
