open import Data.Fin
open import Data.Product
import While.Language as While
import Data.Graph
open import Data.Integer hiding (suc)
module While.Programs.Bogus-3 where

x : Fin 3
x = zero
y : Fin 3
y = suc zero
z : Fin 3
z = suc (suc zero)

open While 5 3
open Data.Graph 5
bogus₃ : Stmt
bogus₃ = (y := lit (+ 2)) (# 0) seq
         (z := lit (+ 1)) (# 1) seq
      while (var x gt lit (+ 0)) , (# 2) do
      (
        (z := var z mul var y) (# 3)        
      ) seq
      (x := var x min lit (+ 1)) (# 4)
