open import Data.Fin
open import Data.Product
open import While-Fun.Language
import Data.Graph
open import Data.Nat
open import Util.List
open import Data.List
open import Data.Integer hiding (suc)
open import Data.String
open import Util.Bag renaming ([] to bag-[])

module While-Fun.Programs.Bogus-1 where
open Unlabeled
module S where
  open Auto ⦃ Data.String._≟_ ⦄ public

bogus : Stmt
bogus = "x" := lit (+ 2) seq
        "y" := lit (+ 4) seq
        "x" := lit (+ 1) seq
        (if var "y" gt var "x"
        then "z" := var "y"
        else "z" := var "y" mul var "y") seq
        "x" := var "z"
        
open Labeled
private
  n : ℕ
  n = 7

variables : Bag String
variables = "x" S.∷ "y" S.∷ "z" S.∷ bag-[]


x : Fin (length (Util.Bag.toList variables))
x = zero
y : Fin (length (Util.Bag.toList variables))
y = # 1
z : Fin (length (Util.Bag.toList variables))
z = # 2

bogus-labelled : WhileProgram
bogus-labelled = record
         { n = n
         ; Var* = variables
         ; Fun* = bag-[]
         ; blocks = (x := lit (+ 2)) (# 0) 𝕍.∷
                    (y := lit (+ 4)) (# 1) 𝕍.∷
                    (x := lit (+ 1)) (# 2) 𝕍.∷
                    bExpr (var y gt var x) (# 3) 𝕍.∷
                    ((z := var y) (# 4)) 𝕍.∷
                    ((z := var y mul var y) (# 5))  𝕍.∷
                    (x := var z) (# 6) 𝕍.∷ 𝕍.[]
         ; functions = 𝕍.[]
         ; labelledProgram = begin []
                             main-is
                               (x := lit (+ 2)) (# 0) seq
                               (y := lit (+ 4)) (# 1) seq
                               (x := lit (+ 1)) (# 2) seq
                               (if (var y gt var x) , (# 3)
                               then (z := var y) (# 4)
                               else (z := var y mul var y) (# 5)) seq
                               (x := var z) (# 6)
                             end       
         }
open Labeled
