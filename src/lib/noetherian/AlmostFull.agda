

module AlmostFull where


open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Data.List
open import Utilities
open import Coinduction
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Sum renaming (_⊎_ to _+_) hiding (map)
open import Data.Empty
open import Function




-- Almost full
data AF (X : Set) (R : X → X → Set) : Set where
  afzt  : ∀(p : ∀ x y → R x y) → AF X R
  afsup : ∀(p : ∀ x → AF X (λ y z → R y z + R x y)) → AF X R

AFEq : Set → Set
AFEq X = AF X _≡_


AF→ : ∀{X S R}(q : ∀{x y} → R x y → S x y) → AF X R → AF X S
AF→ q (afzt p) = afzt (λ x y → q (p x y))
AF→ q (afsup p) =
  afsup (λ x → AF→ (λ { (inj₁ r) → inj₁ (q r) ; (inj₂ r) → inj₂ (q r) }) (p x))

