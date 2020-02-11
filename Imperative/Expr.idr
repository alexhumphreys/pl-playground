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

BinaryOperator : Type -> Type
BinaryOperator a = List (Parser () -> (a -> a -> a) -> Parser (a -> a -> a))

UnaryOperator : Type -> Type
UnaryOperator a = List (Parser () -> (a -> a) -> Parser (a -> a))

data Ops a = BinOp (BinaryOperator a) | UnOp (UnaryOperator a)

ReturnType : Type -> Type
ReturnType a = (BinaryOperator a, BinaryOperator a, BinaryOperator a, UnaryOperator a, UnaryOperator a)

toParserBin : BinaryOperator a -> Parser () -> (a -> a -> a) -> Parser (a -> a -> a)
toParserBin [] y f = fail "couldn't create binary parser"
toParserBin (x :: xs) y f = let p = x y f in
                                p <|> toParserBin xs y f

toParserUn : UnaryOperator a -> Parser () -> (a -> a) -> Parser (a -> a)
toParserUn [] y f = fail "couldn't create unary parser"
toParserUn (x :: xs) y f = let p = x y f in
                               p <|> toParserUn xs y f

buildExpressionParser : (a : Type) -> OperatorTable a -> Parser a -> Parser a
buildExpressionParser a operators simpleExpr =
  foldl (makeParser a) simpleExpr operators
  where
    splitOp : (a : Type) -> Operator a -> ReturnType a -> ReturnType a
    splitOp x (Infix op AssocNone) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, op :: nassoc, prefixx, postfix)
    splitOp x (Infix op AssocLeft) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, op :: lassoc, nassoc, prefixx, postfix)
    splitOp x (Infix op AssocRight) (rassoc, lassoc, nassoc, prefixx, postfix) = (op :: rassoc, lassoc, nassoc, prefixx, postfix)
    splitOp x (Prefix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, op :: prefixx, postfix)
    splitOp x (Postfix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, prefixx, op :: postfix)

    makeParser : (a : Type) -> Parser a -> LO a -> Parser a
    makeParser a term ops =
      let (rassoc,lassoc,nassoc
               ,prefixx,postfix) = foldr (splitOp a) ([],[],[],[],[]) ops
          rassocOp = toParserBin rassoc
          lassocOp = toParserBin lassoc
          nassocOp = toParserBin nassoc
          prefixxOp = toParserUn prefixx
          postfixOp = toParserUn postfix

          termP = do -- pre <- prefixxOp
                     x <- term
                     -- post <- postfixOP
                     pure (x)
               in
          ?baz
