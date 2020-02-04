module Imperative.Lexer

import DataStructures
import Lightyear.Strings

%access export

rIf : Parser ()
rIf = token "if"

rThen : Parser ()
rThen = token "then"

rElse : Parser ()
rElse = token "else"

rWhile : Parser ()
rWhile = token "while"

rDo : Parser ()
rDo = token "do"

rSkip : Parser ()
rSkip = token "skip"

rTrue : Parser ()
rTrue = token "true"

rFalse : Parser ()
rFalse = token "false"

rPlus : Parser ()
rPlus = token "+"

rMinus : Parser ()
rMinus = token "-"

rTimes : Parser ()
rTimes = token "*"

rDivide : Parser ()
rDivide = token "/"

rAssign : Parser ()
rAssign = token ":="

rLT : Parser ()
rLT = token "<"

rGT : Parser ()
rGT = token ">"

rAnd : Parser ()
rAnd = token "and"

rOr : Parser ()
rOr = token "or"

rNot : Parser ()
rNot = token "not"

reservedNames : List String
reservedNames = [ "if"
                , "then"
                , "else"
                , "while"
                , "do"
                , "skip"
                , "true"
                , "false"
                , "not"
                , "and"
                , "or"
                ]
