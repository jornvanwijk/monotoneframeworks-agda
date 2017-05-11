open import Data.Fin
open import Data.Product
import While-Fun.Language as While
import Data.Graph
open import Data.Integer hiding (suc)
open import Data.List
module While-Fun.Programs.Factorial where

x : Fin 5
x = zero
y : Fin 5
y = suc zero
z : Fin 5
z = suc (suc zero)
u : Fin 5
u = # 3
v : Fin 5
v = # 4

open While 10 5 public
open Data.Graph 10
fac : Program
fac = begin
       (proc "fib" ⟨ z ∷ u ∷ [] , v ⟩ single (# 0) is
         if lit (+ 3) gt var z , single (# 1)
         then (v := (var v plus lit (+ 1))) (single (# 2))
         else (call "fib" (var z min lit (+ 1) ∷ var u ∷ []) v (single (# 3)) (single (# 4)) seq
               call "fib" (var z min lit (+ 2) ∷ var v ∷ []) v (single (# 5)) (single (# 6)))
        end single (# 7)) ∷ []
      main-is
        call "fib" (var x ∷ lit (+ 0) ∷ []) y (single (# 8)) (single (# 9))
      end

result : List (Lab₁ × Lab₁)
result = flow⋆ fac
{-


(y := var x) (# 0) seq
      (z := lit (+ 1)) (# 1) seq
      while (var y gt lit (+ 1)) , (# 2) do
      (
        (z := var z mul var y) (# 3) seq
        (y := var y min lit (+ 1)) (# 4)
        
      ) seq
      (y := lit (+ 0)) (# 5)
-}
