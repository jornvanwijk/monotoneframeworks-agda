

module Examples.Pauli where

open import Relation.Binary.PropositionalEquality 
open import Relation.Binary.Core 
open import Relation.Nullary

open import Data.List
open import Data.Sum
open import Data.Empty

open import Utilities.ListProperties 
  using (_∈_ ; here ; there)


data Pauli : Set where
  X : Pauli
  Y : Pauli
  Z : Pauli
  I : Pauli


listPauli : List Pauli
listPauli = X ∷ Y ∷ Z ∷ I ∷ []


allPauli : (p : Pauli) → p ∈ listPauli
allPauli X = here
allPauli Y = there here
allPauli Z = there (there here)
allPauli I = there (there (there here))



_==_ : (p₁ p₂ : Pauli) → p₁ ≡ p₂ ⊎ (p₁ ≡ p₂ → ⊥)
X == X = inj₁ refl
X == Y = inj₂ (λ { () })
X == Z = inj₂ (λ { () })
X == I = inj₂ (λ { () })
Y == X = inj₂ (λ { () })
Y == Y = inj₁ refl
Y == Z = inj₂ (λ { () })
Y == I = inj₂ (λ { () })
Z == X = inj₂ (λ { () })
Z == Y = inj₂ (λ { () })
Z == Z = inj₁ refl
Z == I = inj₂ (λ { () })
I == X = inj₂ (λ { () })
I == Y = inj₂ (λ { () })
I == Z = inj₂ (λ { () })
I == I = inj₁ refl




_⋅_ : Pauli → Pauli → Pauli
X ⋅ X = I
X ⋅ Y = Z
X ⋅ Z = Y
Y ⋅ X = Z
Y ⋅ Y = I
Y ⋅ Z = X
Z ⋅ X = Y
Z ⋅ Y = X
Z ⋅ Z = I
a ⋅ I = a
I ⋅ a = a


⋅-comm : (p₁ p₂ : Pauli) → p₁ ⋅ p₂ ≡ p₂ ⋅ p₁
⋅-comm X X = refl
⋅-comm X Y = refl
⋅-comm X Z = refl
⋅-comm X I = refl
⋅-comm Y X = refl
⋅-comm Y Y = refl
⋅-comm Y Z = refl
⋅-comm Y I = refl
⋅-comm Z X = refl
⋅-comm Z Y = refl
⋅-comm Z Z = refl
⋅-comm Z I = refl
⋅-comm I X = refl
⋅-comm I Y = refl
⋅-comm I Z = refl
⋅-comm I I = refl




open import Data.Fin
open import Data.Fin.Dec
open import Data.Nat
open import Data.Bool
open import Relation.Nullary.Decidable

p2f : Pauli → Fin 4
p2f X = zero
p2f Y = suc zero
p2f Z = suc (suc zero)
p2f I = suc (suc (suc zero))

f2p : Fin 4 → Pauli
f2p zero = X
f2p (suc zero) = Y
f2p (suc (suc zero)) = Z
f2p (suc (suc (suc zero))) = I
f2p (suc (suc (suc (suc ()))))

fp-inv : ∀ p → f2p (p2f p) ≡ p
fp-inv X = refl
fp-inv Y = refl
fp-inv Z = refl
fp-inv I = refl







