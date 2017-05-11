open import Data.Fin
open import Data.Product
open import While.Language 
import Data.Graph
open import Data.Integer hiding (suc)
module While.Programs.Factorial where

open Unlabeled

fac : Stmt
fac = "y" := var "x" seq
      "z" := lit (+ 1) seq
      while var "y" gt lit (+ 1) do
      (
        "x" := var "z" mul var "y" seq
        "y" := var "y" min lit (+ 1)
      ) seq
      "y" := lit (+ 0)

open Labeled
open Generated fac renaming (whileProgram to fac-labeled) public


--open Labeled fac public 
{-
Wil:

Var* = y ∷ x ∷ z ∷ []
blocks = 
-}
--open Labeled fac public

--open Labeled fac' public renaming (labelledProgram to fac)
{-
Var* = "z" ∷ "x" ∷ "y" ∷ []


blocks = 2 := lit (+ 0)) 5
  𝕍.∷   2 := var 2 min lit (+ 1)) 4
  𝕍.∷  (1 := var 0 mul var 2) 3
  𝕍.∷  bExpr (lit (+ 1) gt var 2) 2    --- <-  gt omgedraaid!
  𝕍.∷  (zero := lit (+ 1)) 1
  𝕍.∷  2 := var 1) 0
  𝕍.∷ 𝕍.[]

x : Fin 3
x = zero
y : Fin 3
y = suc zero
z : Fin 3
z = suc (suc zero)

open While 6 3
open Data.Graph 6
fac : Stmt
fac = (y := var x) (# 0) seq
      (z := lit (+ 1)) (# 1) seq
      while (var y gt lit (+ 1)) , (# 2) do
      (
        (z := var z mul var y) (# 3) seq
        (y := var y min lit (+ 1)) (# 4)
        
      ) seq
      (y := lit (+ 0)) (# 5)
-}
