import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

data Assoc = AssocNone
           | AssocLeft
           | AssocRight

data Operator a = Infix (Parser (a -> a -> a)) Assoc
                | Prefix (Parser (a -> a))
                | Postfix (Parser (a -> a))

LO : Type -> Type
LO a = List (Operator a)

OperatorTable : Type -> Type
OperatorTable a = List (LO a)

BinaryOperator : Type -> Type
BinaryOperator a = List (Parser (a -> a -> a))

UnaryOperator : Type -> Type
UnaryOperator a = List (Parser (a -> a))

data Ops a = BinOp (BinaryOperator a) | UnOp (UnaryOperator a)

ReturnType : Type -> Type
ReturnType a = (BinaryOperator a, BinaryOperator a, BinaryOperator a, UnaryOperator a, UnaryOperator a)

toParserBin : BinaryOperator a -> Parser (a -> a -> a)
toParserBin [] = fail "couldn't create binary parser"
toParserBin (x :: xs) = x <|>| toParserBin xs

toParserUn : UnaryOperator a -> Parser (a -> a)
toParserUn [] = fail "couldn't create unary parser"
toParserUn (x :: xs) = x <|>| toParserUn xs

ambigious : (assoc : String) -> (op : Parser (a -> a -> a)) -> Parser a
ambigious assoc op = do op
                        fail ("ambiguous use of a " ++ assoc ++ " associative operator")

record Ambiguous where
    constructor MkAmbiguous
    ambigiousRight, ambigiousLeft, ambigiousNon : Parser a

mutual
  mkRassocP : (ambig : Ambiguous) -> (rassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkRassocP ambig rassocOp termP x =
    do f <- rassocOp
       y <- do z <- termP ; mkRassocP1 ambig rassocOp termP z
       pure (f x y)

  mkRassocP1 : (ambig : Ambiguous) -> (rassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkRassocP1 ambig rassocOp termP x = (mkRassocP ambig rassocOp termP x) <|> pure x

mutual

  mkLassocP : (ambig : Ambiguous) -> (lassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkLassocP ambig lassocOp termP x =
    do f <- lassocOp
       y <- termP
       mkLassocP1 ambig lassocOp termP (f x y)

  mkLassocP1 : (ambig : Ambiguous) -> (lassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkLassocP1 ambig lassocOp termP x = mkLassocP ambig lassocOp termP x <|> pure x

mkNassocP : (ambig : Ambiguous) -> (nassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
mkNassocP ambig nassocOp termP x =
  do f <- nassocOp
     y <- termP
     pure (f x y)

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

          ambig = MkAmbiguous (ambigious "right" rassocOp) (ambigious "left" lassocOp) (ambigious "non" nassocOp)

          prefixxP = prefixxOp <|> pure id

          postfixP = postfixOp <|> pure id

          termP = do pre <- prefixxP
                     x <- term
                     post <- postfixP
                     pure (post (pre x))

          rassocP = mkRassocP ambig rassocOp termP
          rassocP1 = mkRassocP1 ambig rassocOp termP

          lassocP = mkLassocP ambig lassocOp termP
          lassocP1 = mkLassocP1 ambig lassocOp termP

          nassocP = mkNassocP ambig nassocOp termP

          test = do z <- termP
                    ?bar
               in
          ?baz
