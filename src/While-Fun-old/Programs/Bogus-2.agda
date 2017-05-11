open import Data.Fin
open import Data.Product
import While.Language as While
import Data.Graph
open import Data.Integer
module While.Programs.Bogus-2 where
  
x : Fin 4
x = # 0
y : Fin 4
y = # 1
a : Fin 4
a = # 2
b : Fin 4
b = # 3

open While 5 4
open Data.Graph 5
bogus₂ : Stmt
bogus₂ = (x := (var a plus var b)) (# 0) seq
        (y := (var a mul var b)) (# 1) seq
        while ((var y gt (var a plus var b)) , # 2) do
        (
        (a := (var a plus lit (+ 1))) (# 3) seq
        (x := (var a plus var b)  ) (# 4)
        )
 

stmt-0 : Block
stmt-0 = (x := lit (+ 4)) (# 0)
stmt-1 : Block
stmt-1 = (y := (var a mul var b)) (# 1)
stmt-2 : Block
stmt-2 = bExpr (var y gt (var a plus var b)) (# 2)
stmt-3 : Block
stmt-3 = (a := (var a plus lit (+ 1))) (# 3)
stmt-4 : Block
stmt-4 = (x := (var a plus var b)  ) (# 4)
