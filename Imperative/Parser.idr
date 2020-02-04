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
