import Level

module LatticeTheory.Z-Top where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Unit hiding (_≟_)
open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Integer renaming (_⊔_ to max ; _⊓_ to min ; _≟_ to _≟ℤ_)
open import Data.Bool renaming (_≟_ to _≟𝔹_)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product

data ℤ⊤⊥ : Set where
  top : ℤ⊤⊥
  in-ℤ : (i : ℤ) → ℤ⊤⊥
  bot : ℤ⊤⊥

open import Data.String hiding (_≟_)

showℤ⊤⊥ : ℤ⊤⊥ → String
showℤ⊤⊥ top = "⊤"
showℤ⊤⊥ (in-ℤ i) = Data.Integer.show i
showℤ⊤⊥ bot = "⊥"


mapℤ : (f : ℤ → ℤ) → ℤ⊤⊥ → ℤ⊤⊥
mapℤ f top = top
mapℤ f (in-ℤ i) = in-ℤ (f i) 
mapℤ f bot = bot

mapℤ₂ : (_op_ : ℤ → ℤ → ℤ) → ℤ⊤⊥ → ℤ⊤⊥ → ℤ⊤⊥
mapℤ₂ f top y = top
mapℤ₂ f (in-ℤ i) top = top
mapℤ₂ f (in-ℤ i) (in-ℤ i₁) = in-ℤ (f i i₁)
mapℤ₂ f (in-ℤ i) bot = bot
mapℤ₂ f bot y = bot 

_plusℤ_ : ℤ⊤⊥ → ℤ⊤⊥ → ℤ⊤⊥
_plusℤ_ = mapℤ₂ _+_

_minℤ_ : ℤ⊤⊥ → ℤ⊤⊥ → ℤ⊤⊥
_minℤ_ = mapℤ₂ _-_

_mulℤ_ : ℤ⊤⊥ → ℤ⊤⊥ → ℤ⊤⊥
_mulℤ_ = mapℤ₂ _*_


ℤ⊤⊥ᴸ : BoundedSemiLattice Level.zero
ℤ⊤⊥ᴸ = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set 
  ℂ = ℤ⊤⊥
  open Algebra.FunctionProperties {A = ℂ} _≡_
  _≟_ : Decidable {A = ℂ} _≡_
  top ≟ top = yes refl
  top ≟ in-ℤ i = no (λ{()})
  top ≟ bot = no (λ{()})
  in-ℤ i ≟ top = no (λ{()})
  in-ℤ i ≟ in-ℤ i₁ with i ≟ℤ i₁
  in-ℤ i ≟ in-ℤ i₁ | yes p = yes (cong in-ℤ p)
  in-ℤ i ≟ in-ℤ i₁ | no ¬p = no (λ{ refl → contradiction refl ¬p})
  in-ℤ i ≟ bot = no (λ{()})
  bot ≟ top = no (λ{()})
  bot ≟ in-ℤ i = no (λ{()})
  bot ≟ bot = yes refl
  _⊔_ : Op₂ ℂ
  top ⊔ y = top
  y ⊔ top = top
  in-ℤ i ⊔ in-ℤ j with i ≟ℤ j
  in-ℤ i ⊔ in-ℤ j | yes p = in-ℤ i
  in-ℤ i ⊔ in-ℤ j | no ¬p = top
  in-ℤ i ⊔ bot = in-ℤ i
  bot ⊔ a = a
  ⊥ : ℂ 
  ⊥ = bot
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal top = refl
  ⊥-isMinimal (in-ℤ i) = refl
  ⊥-isMinimal bot = refl
  ⊔-idem : Idempotent _⊔_
  ⊔-idem top = refl
  ⊔-idem (in-ℤ i) with i ≟ℤ i
  ⊔-idem (in-ℤ i) | yes p = refl
  ⊔-idem (in-ℤ i) | no ¬p = ⊥-elim (¬p refl)
  ⊔-idem bot = refl
  ⊔-comm : Commutative _⊔_
  ⊔-comm top top = refl
  ⊔-comm top (in-ℤ i) = refl
  ⊔-comm top bot = refl
  ⊔-comm (in-ℤ i) top = refl
  ⊔-comm (in-ℤ i) (in-ℤ j) with j ≟ℤ i | i ≟ℤ j
  ⊔-comm (in-ℤ i) (in-ℤ j) | yes p | yes p₁ = cong in-ℤ p₁
  ⊔-comm (in-ℤ i) (in-ℤ j) | yes p | no ¬p = ⊥-elim (¬p (sym p))
  ⊔-comm (in-ℤ i) (in-ℤ j) | no ¬p | yes p = ⊥-elim (¬p (sym p))
  ⊔-comm (in-ℤ i) (in-ℤ j) | no ¬p | no ¬p₁ = refl
  ⊔-comm (in-ℤ i) bot = refl
  ⊔-comm bot top = refl
  ⊔-comm bot (in-ℤ i) = refl
  ⊔-comm bot bot = refl
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong refl refl = refl
  ⊔-assoc : Associative _⊔_
  ⊔-assoc top y z = refl
  ⊔-assoc (in-ℤ i) top z = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) top with i ≟ℤ j
  ⊔-assoc (in-ℤ i) (in-ℤ j) top | yes p = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) top | no ¬p = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) (in-ℤ k) with i ≟ℤ j | j ≟ℤ k
  ⊔-assoc (in-ℤ i) (in-ℤ .i) (in-ℤ .i) | yes refl | yes refl = refl
  ⊔-assoc (in-ℤ i) (in-ℤ .i) (in-ℤ k) | yes refl | no ¬p with i ≟ℤ k
  ⊔-assoc (in-ℤ i) (in-ℤ .i) (in-ℤ k) | yes refl | no ¬p | yes p = ⊥-elim (¬p p)
  ⊔-assoc (in-ℤ i) (in-ℤ .i) (in-ℤ k) | yes refl | no ¬p₁ | no ¬p = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) (in-ℤ .j) | no ¬p | yes refl with i ≟ℤ j -- not really understand why we again have to match, probably because of associativity?
  ⊔-assoc (in-ℤ i) (in-ℤ j) (in-ℤ .j) | no ¬p | yes refl | yes p = ⊥-elim (¬p p)
  ⊔-assoc (in-ℤ i) (in-ℤ j) (in-ℤ .j) | no ¬p₁ | yes refl | no ¬p = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) (in-ℤ k) | no ¬p | no ¬p₁ = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) bot with i ≟ℤ j
  ⊔-assoc (in-ℤ i) (in-ℤ j) bot | yes p = refl
  ⊔-assoc (in-ℤ i) (in-ℤ j) bot | no ¬p = refl
  ⊔-assoc (in-ℤ i) bot top = refl
  ⊔-assoc (in-ℤ i) bot (in-ℤ j) with i ≟ℤ j
  ⊔-assoc (in-ℤ i) bot (in-ℤ j) | yes p = refl
  ⊔-assoc (in-ℤ i) bot (in-ℤ j) | no ¬p = refl
  ⊔-assoc (in-ℤ i) bot bot = refl
  ⊔-assoc bot top z = refl
  ⊔-assoc bot (in-ℤ i) top = refl
  ⊔-assoc bot (in-ℤ i) (in-ℤ j)  with i ≟ℤ j
  ⊔-assoc bot (in-ℤ i) (in-ℤ j) | yes p = refl
  ⊔-assoc bot (in-ℤ i) (in-ℤ j) | no ¬p = refl
  ⊔-assoc bot (in-ℤ i) bot = refl
  ⊔-assoc bot bot top = refl
  ⊔-assoc bot bot (in-ℤ i) = refl
  ⊔-assoc bot bot bot = refl

  lemma : {i j : ℤ} → in-ℤ i ⊑ in-ℤ j → i ≡ j
  lemma {i} {j} p with i ≟ℤ j
  lemma {i} {j} p₁ | yes p = p
  lemma {i} {j} () | no ¬p

  -- top is accessible because there does not exist anything greater than top.
  acc-top : Acc _⊐_ top
  acc-top = acc (λ{ y (a , b) → ⊥-elim (b a)})


  -- everything greater than i is accessible because
  acc-i : ∀{i} → Acc _⊐_ (in-ℤ i)
  acc-i {i} = acc (λ{ top x → acc-top  -- top is accessible
                  ; (in-ℤ i₁) (a , b) → ⊥-elim (b (cong in-ℤ (lemma a))) -- there is no i ‌≠ j such that j is greater than i
                  ; bot (a , b) → ⊥-elim (b a)}) -- bot is not greater than i

  -- everything greater than bot is accessible because
  acc-bot : Acc _⊐_ bot
  acc-bot = acc (λ{ top (a , b) → acc-top -- top is accessible
                  ; (in-ℤ i) (a , b) → acc-i  -- all i are accessible
                  ; bot (a , b) → ⊥-elim (b a)}) -- bot is not greater than bot

  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded top = acc-top
  ⊐-isWellFounded (in-ℤ i) = acc-i
  ⊐-isWellFounded bot = acc-bot
