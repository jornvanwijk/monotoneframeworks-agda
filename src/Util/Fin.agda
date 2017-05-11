


module Util.Fin where

module ℕ where
  open import Data.Nat public
  open import Data.Nat.DivMod public
  
module ℕ⁺ where

  record ℕ⁺ : Set where
    constructor n⁺
    field
      n : ℕ.ℕ
      .>0 : n ℕ.> 0

  open import Data.Nat.Properties
  _+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  _+_ (n⁺ n >0) (n⁺ n₁ >1) = n⁺ (n ℕ.+ n₁) (>0 +-mono ℕ.z≤n)

  _*_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  n⁺ n >0 * n⁺ n₁ >1 = n⁺ (n ℕ.* n₁) (>0 *-mono >1)

  _div_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  n⁺ n >0 div n⁺ n₁ >1 with (n ℕ.divMod n₁) {{!!}}
  n⁺ n >0 div n⁺ n₁ >1 | ℕ.result quotient remainder property = {!quotient!}

open import Data.Fin
open import Data.Fin.Properties





_*_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (m ℕ.* n)
zero * zero = zero
_*_ {m} {ℕ.suc n} zero (suc j) = {!suc (_*_ {m} {n} zero j)!} -- suc (zero * j) --j
suc i * j = {!suc i + i * j!} --suc (i * j)



blah : (m n i j : ℕ.ℕ) → i ℕ.< m → j ℕ.< n → i ℕ.* j ℕ.< m ℕ.* n
blah m n i j x x₁ = {!!}

