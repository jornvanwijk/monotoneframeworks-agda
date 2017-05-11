open import Data.Fin
open import Data.Product
open import While-Fun.Language 
import Data.Graph
open import Data.Integer hiding (suc)
module While-Fun.Programs.Factorial where
open Labeled
open import Data.List
open import Util.Bag renaming ([] to []B)
open Auto renaming (_∷_ to _∷B_ )


open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

instance
  _≟String_ : ∀{x y : String} → Relation.Nullary.Dec (x ≡ y)
  _≟String_ {x} {y} = Data.String._≟_ x y


fac : WhileProgram
WhileProgram.n fac = 10
WhileProgram.Var* fac = "x" ∷B "y" ∷B "u" ∷B "z" ∷B "v" ∷B []B
WhileProgram.Fun* fac = "fib" ∷B []B
WhileProgram.blocks fac =      entry (# 0) ((# 3 ∷ # 2 ∷ [])) (# 4) (# 0) (if ((lit (+ 3) gt var (# 3)) , (# 1))
                                then ((# 4) := var (# 2) plus lit (+ 1)) (# 2)
                                else (
                                   call (# 3) (# 0) (# 4) (var (# 3) min lit (+ 1) ∷ var (# 2) ∷ []) (# 4) seq
                                   call (# 5) (# 0) (# 6) (var (# 3) min lit (+ 2) ∷ var (# 4) ∷ []) (# 4)
                                )) (# 7)
                          𝕍.∷ bExpr ((lit (+ 3) gt var (# 3))) (# 1)
                          𝕍.∷ ((# 4) := var (# 2) plus lit (+ 1)) (# 2)
                          𝕍.∷ call (# 3) (# 0) (# 4) ((var (# 3) min lit (+ 1) ∷ var (# 2) ∷ [])) (# 4)
                          𝕍.∷ return (# 3) (# 0) (# 4) ((var (# 3) min lit (+ 1) ∷ var (# 2) ∷ [])) (# 4)
                          𝕍.∷ call (# 5) (# 0) (# 6) (var (# 3) min lit (+ 2) ∷ var (# 4) ∷ []) (# 4)
                          𝕍.∷ return (# 5) (# 0) (# 6) (var (# 3) min lit (+ 2) ∷ var (# 4) ∷ []) (# 4)
                          𝕍.∷ exit (# 0) ((# 3 ∷ # 2 ∷ [])) (# 4) (# 0) (if ((lit (+ 3) gt var (# 3)) , (# 1))
                                then ((# 4) := var (# 2) plus lit (+ 1)) (# 2)
                                else (
                                   call (# 3) (# 0) (# 4) (var (# 3) min lit (+ 1) ∷ var (# 2) ∷ []) (# 4) seq
                                   call (# 5) (# 0) (# 6) (var (# 3) min lit (+ 2) ∷ var (# 4) ∷ []) (# 4)
                                )) (# 7)
                          𝕍.∷ call (# 8) (# 0) (# 9) (var (# 0) ∷ lit (+ 0) ∷ []) (# 1) 
                          𝕍.∷ return (# 8) (# 0) (# 9) (var (# 0) ∷ lit (+ 0) ∷ []) (# 1)
                          𝕍.∷ 𝕍.[]
WhileProgram.functions fac = (proc (# 0) ⟨ (# 3 ∷ # 2 ∷ []) , (# 4) ⟩ (# 0)
                             is if ((lit (+ 3) gt var (# 3)) , (# 1))
                                then ((# 4) := var (# 2) plus lit (+ 1)) (# 2)
                                else (
                                   call (# 3) (# 0) (# 4) (var (# 3) min lit (+ 1) ∷ var (# 2) ∷ []) (# 4) seq
                                   call (# 5) (# 0) (# 6) (var (# 3) min lit (+ 2) ∷ var (# 4) ∷ []) (# 4)
                                )
                             end (# 7)) 𝕍.∷ 𝕍.[]
WhileProgram.labelledProgram fac = begin (𝕍.toList (WhileProgram.functions fac)) main-is call (# 8) (# 0) (# 9) (var (# 0) ∷ lit (+ 0) ∷ []) (# 1) end

