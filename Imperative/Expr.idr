import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

data Assoc = AssocNone
           | AssocLeft
           | AssocRight

-- Parser () -> (a -> a -> a) -> Parser (a -> a -> a)
data Operator a = Infix (Parser () -> (a -> a -> a) -> Parser (a -> a -> a)) Assoc
                | Prefix (Parser () -> (a -> a) -> Parser (a -> a))
                | Postfix (Parser () -> (a -> a) -> Parser (a -> a))

LO : Type -> Type
LO a = List (Operator a)

OperatorTable : Type -> Type
OperatorTable a = List (LO a)

record Associations type where
       constructor MkAssociations
       rassoc : List (Parser () -> (type -> type -> type) -> Parser (type -> type -> type))
       lassoc : List (Parser () -> (type -> type -> type) -> Parser (type -> type -> type))
       nassoc : List (Parser () -> (type -> type -> type) -> Parser (type -> type -> type))
       prefixx : List (Parser () -> (type -> type) -> Parser (type -> type))
       postfix : List (Parser () -> (type -> type) -> Parser (type -> type))


buildExpressionParser : (a : Type) -> OperatorTable a -> Parser a -> Parser a
buildExpressionParser a operators simpleExpr = ?buildExpressionParser_rhs
  where
                        {-
    makeParser : Parser ctor -> List Operator -> ctor
    makeParser term ops = ?foo
                        -- (rassoc,lassoc,nassoc,prefix,postfix)
                        -}
    splitOp : (a : Type) -> Operator a -> Associations a -> Associations a
    splitOp x (Infix op AssocNone) acc = record { nassoc = (op :: (nassoc acc)) } acc
    splitOp x (Infix op AssocLeft) acc = record { lassoc = (op :: (lassoc acc)) } acc
    splitOp x (Infix op AssocRight) acc = record { rassoc = (op :: (rassoc acc)) } acc
    splitOp x (Prefix op) acc = record { prefixx = (op :: (prefixx acc)) } acc
    splitOp x (Postfix op) acc = record { postfix = (op :: (postfix acc)) } acc
