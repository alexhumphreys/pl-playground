module DataStructures

%access public export
data BBinOp = And | Or
Show BBinOp where
  show And = "AND"
  show Or = "OR"

data RBinOp = Greater | Less
Show RBinOp where
  show Greater = "GREATER"
  show Less = "LESS"

data ABinOp = Add
            | Subtract
            | Multiply
            | Divide
Show ABinOp where
  show Add = "ADD"
  show Subtract = "SUBTRACT"
  show Multiply = "MULTIPLY"
  show Divide = "DIVIDE"

data AExpr = Var String
           | IntConst Integer
           | Neg AExpr
           | ABinary ABinOp AExpr AExpr
Show AExpr where
  show (Var a) = "VAR " ++ a
  show (IntConst i) = "INTCONST " ++ (show i)
  show (Neg a) = "NEG " ++ (show a)
  show (ABinary o l r) = "ABINARY " ++ (show o) ++ (show l) ++ (show r)

data BExpr = BoolConst Bool
           | BNot BExpr
           | BBinary BBinOp BExpr BExpr
           | RBinary RBinOp AExpr AExpr
Show BExpr where
  show (BoolConst b) = "BOOLCONST " ++ (show b)
  show (BNot b) = "BNOT " ++ (show b)
  show (BBinary o l r) = "BBINARY " ++ (show o) ++ (show l) ++ (show r)
  show (RBinary o l r) = "RBINARY " ++ (show o) ++ (show l) ++ (show r)

data Stmt = Seq (List Stmt)
          | Assign String AExpr
          | If BExpr Stmt Stmt
          | While BExpr Stmt
          | Skip
Show Stmt where
  show (Seq x) = concatMap (\s => show s ++ "\n") x
  show (Assign s a) = "ASSIGN " ++  s ++ (show a)
  show (If b t f) = "IF " ++ (show b) ++ (show t) ++ (show f)
  show (While b s) = "While " ++ (show b) ++ (show s)
  show Skip = "SKIP"
