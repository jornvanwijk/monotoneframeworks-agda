
module Examples.Combinators where


open import Combinators
open import Finiteness

open import Data.Product
open import Data.List hiding (product ; sum)
open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Data.Unit
open import Examples.Pauli

open import Utilities.ListProperties

-- Bool is listable
BoolListable : Listable Bool
BoolListable = true ∷ false ∷ [] , 
  (λ { true → here ; false → there here })


-- Pauli is Listable
PauliListable : Listable Pauli
PauliListable = listPauli , allPauli


-- Bool × Pauli is listable
Pauli×Bool : Listable (Bool × Pauli)
Pauli×Bool with product 
                 (lstbl2subset BoolListable) 
                 (lstbl2subset PauliListable) 
Pauli×Bool | bp , s , c = bp , (λ x → c x (tt , tt))


-- Bool ⊎ Pauli is listable 
open import Data.Sum
Pauli⊎Bool : Listable (Bool ⊎ Pauli)
Pauli⊎Bool with sum 
                 (lstbl2subset BoolListable) 
                 (lstbl2subset PauliListable) 
... | bp , s , c = bp , (λ { (inj₁ x) → c _ tt ; 
                             (inj₂ y) → c _ tt })
