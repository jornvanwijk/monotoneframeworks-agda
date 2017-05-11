open import Data.Integer as ℤ
open import Data.Nat as ℕ

module Util.Integer where


Positive : ℤ → Set
Positive x = + 0 ℤ.≤ x

toℕ : (x : ℤ) → Positive x → ℕ
toℕ (+_ n) (+≤+ m≤n) = n
toℕ (-[1+_] n) ()


preservation-positivity₁ : {x : ℤ} → {y : ℤ} → Positive x → y ℤ.≤ x → Positive (x - y)
preservation-positivity₁ x₁ -≤+ = +≤+ z≤n
preservation-positivity₁ () (-≤- n≤m)
preservation-positivity₁ x₁ (+≤+ z≤n) = +≤+ z≤n
preservation-positivity₁ {.(+ ℕ.suc _)} {.(+ 1)} x₁ (+≤+ (s≤s z≤n)) = +≤+ z≤n
preservation-positivity₁ {.(+ ℕ.suc (ℕ.suc _))} {.(+ ℕ.suc (ℕ.suc _))} x₁ (+≤+ (s≤s (s≤s m≤n))) = preservation-positivity₁ (+≤+ z≤n) (+≤+ (s≤s m≤n))


suc-preserves-positivity : {x : ℤ} → Positive x → Positive (ℤ.suc x)
suc-preserves-positivity (+≤+ m≤n) = +≤+ z≤n

open import Relation.Binary.PropositionalEquality
ℤ≡-to-ℕ≡ : {a b : ℕ} → ℤ.+ a ≡ ℤ.+ b → a ≡ b
ℤ≡-to-ℕ≡ {a} {.a} refl = refl

ℕ≡-to-ℤ≡ : {a b : ℕ} → a ≡ b → ℤ.+ a ≡ ℤ.+ b
ℕ≡-to-ℤ≡ refl = refl

ℤ+-+ : {a b : ℕ} → ℤ.+ (a ℕ.+ b) ≡ ℤ.+ a ℤ.+ ℤ.+ b
ℤ+-+ {zero} {b} = refl
ℤ+-+ {ℕ.suc a} {b} = refl
open import Data.Integer.Properties
open ≡-Reasoning

{-

a∸b+b≡a : (a b : ℕ) → b ≤ a → (a ∸ b) + b ≡ a
a∸b+b≡a a zero x = +-right-identity a
a∸b+b≡a zero (suc b) ()
a∸b+b≡a (suc a) (suc b) (s≤s x) = trans (+-suc (a ∸ b) b) (cong suc (a∸b+b≡a a b x))

-}
open import Data.Nat.Properties.Simple

ℤsuc-to-ℕsuc : ∀ n → ℤ.suc (ℤ.+ n) ≡ ℤ.+ ℕ.suc n
ℤsuc-to-ℕsuc n = refl

module R where
  open import Algebra
  open import Algebra.Structures
  open CommutativeRing commutativeRing using (isCommutativeRing) 
  open IsCommutativeRing isCommutativeRing public
{- open AbelianGroup +-abelianGroup using (isAbelianGroup) -- (+-comm)
open IsAbelianGroup isAbelianGroup using () -}

open import Algebra.FunctionProperties

-to-plus : ∀ a → - (- a) ≡ a
-to-plus (+_ zero) = refl
-to-plus (+_ (ℕ.suc n)) = refl
-to-plus (-[1+_] n) = refl

open import Data.Product 
-swap : ∀ a b → a - b ≡ - (b - a)
-swap (+_ zero) (+_ zero) = refl
-swap (+_ zero) (+_ (ℕ.suc m)) = cong -[1+_] (sym (+-right-identity m))
-swap (+_ (ℕ.suc n)) (+_ zero) = cong (λ y → + ℕ.suc y) (+-right-identity n)
-swap (+_ (ℕ.suc n)) (+_ (ℕ.suc m)) = ⊖-swap n m
-swap (+_ zero) (-[1+_] zero) = refl
-swap (+_ zero) (-[1+_] (ℕ.suc m)) = refl
-swap (+_ (ℕ.suc n)) (-[1+_] m) = cong (λ y → + ℕ.suc y) (trans (+-suc n m) (cong ℕ.suc (+-comm n m)))
-swap (-[1+_] zero) (+_ zero) = refl
-swap (-[1+_] zero) (+_ (ℕ.suc n)) = cong -[1+_] (+-comm 1 n)
-swap (-[1+_] zero) (-[1+_] zero) = refl
-swap (-[1+_] zero) (-[1+_] (ℕ.suc n)) = refl
-swap (-[1+_] (ℕ.suc n)) (+_ zero) = refl
-swap (-[1+_] (ℕ.suc n)) (+_ (ℕ.suc n₁)) = cong -[1+_] (+-comm (ℕ.suc (ℕ.suc n)) n₁)
-swap (-[1+_] (ℕ.suc n)) (-[1+_] zero) = refl
-swap (-[1+_] (ℕ.suc n)) (-[1+_] (ℕ.suc n₁)) = ⊖-swap n₁ n

+--assoc : (a b c : ℤ) → (a ℤ.- b) ℤ.+ c ≡ a ℤ.- (b ℤ.- c)
+--assoc a b c = trans (R.+-assoc a (- b) c) (cong (ℤ._+_ a) (trans (R.+-comm (- b) c) (-swap c b) ))

open import Function 
ℤ+-suc : ∀ m n → m ℤ.+ ℤ.suc n ≡ ℤ.suc (m ℤ.+ n)
ℤ+-suc (+_ n) (+_ m) = cong +_ (+-suc n m)
ℤ+-suc (+_ zero) (-[1+_] zero) = refl
ℤ+-suc (+_ (ℕ.suc n)) (-[1+_] zero) = cong (+_ ∘ ℕ.suc) (+-right-identity n)
ℤ+-suc (+_ zero) (-[1+_] (ℕ.suc m)) = refl
ℤ+-suc (+_ (ℕ.suc n)) (-[1+_] (ℕ.suc m)) = ℤ+-suc -[1+ m ] (+ n)
ℤ+-suc (-[1+_] zero) (+_ zero) = refl
ℤ+-suc (-[1+_] zero) (+_ (ℕ.suc n)) = refl
ℤ+-suc (-[1+_] zero) (-[1+_] zero) = refl
ℤ+-suc (-[1+_] zero) (-[1+_] (ℕ.suc n)) = refl
ℤ+-suc (-[1+_] (ℕ.suc n)) (+_ zero) = refl
ℤ+-suc (-[1+_] (ℕ.suc n)) (+_ (ℕ.suc n₁)) = ℤ+-suc -[1+ n ] (+ n₁)
ℤ+-suc (-[1+_] (ℕ.suc n)) (-[1+_] zero) = cong (-[1+_] ∘ ℕ.suc) (sym (+-right-identity n))
ℤ+-suc (-[1+_] (ℕ.suc n)) (-[1+_] (ℕ.suc n₁)) = cong (-[1+_] ∘ ℕ.suc) (sym (+-suc n n₁))
{-zero    n = refl
ℤ+-suc (suc m) n = cong suc (+-suc m n)
-}
ℤ⊖- : (a b : ℕ) → a ℤ.⊖ b ℤ.+ ℤ.+ b ≡ ℤ.+ a
ℤ⊖- a zero = cong +_ (+-right-identity a)
ℤ⊖- zero (ℕ.suc b) = n⊖n≡0 b
ℤ⊖- (ℕ.suc a) (ℕ.suc b) = trans (ℤ+-suc (a ⊖ b) (ℤ.+ b)) (cong ℤ.suc (ℤ⊖- a b))

{-
ℤ⊖-' : (a b : ℕ) → + a ℤ.+ (b ℤ.⊖ b) ≡ ℤ.+ a
ℤ⊖-' a b = trans (cong (ℤ._+_ (+ a)) (n⊖n≡0 b)) (cong (λ x → + x) (+-right-identity a))
-}

⊖-to-- : (a b : ℕ) → a ⊖ b ≡ + a - (+ b)
⊖-to-- zero zero = refl
⊖-to-- zero (ℕ.suc b) = refl
⊖-to-- (ℕ.suc a) zero = cong (+_ ∘ ℕ.suc) (sym (+-right-identity a))
⊖-to-- (ℕ.suc a) (ℕ.suc b) = refl



open RingSolver
open import Algebra

example : + 4 - + 2 ≡ + 2
example = solve 0 (con (+ 4) :- con (+ 2) , con (+ 2)) refl

example-with-vars : (x : ℤ) → x - + 4 ≡ - (+ 4 - x)
example-with-vars = solve 1 (λ x → x :- con (+ 4) , :- (con (+ 4) :- x) ) refl



ℤ⊖-outside : (n a b : ℕ) → n ℤ.⊖ a ℤ.+ (b ℤ.⊖ n) ≡ b ℤ.⊖ a
ℤ⊖-outside n a b = 
 begin
 n ℤ.⊖ a ℤ.+ (b ℤ.⊖ n)
 ≡⟨ cong₂ ℤ._+_ (⊖-to-- n a) (⊖-to-- b n) ⟩
 + n - (+ a) ℤ.+ (+ b - (+ n))
 ≡⟨ solve 3 (λ n a b → n :- a :+ (b :- n) , b :- a) (λ {x} {x₁} {x₂} → refl) (+ n) (+ a) (+ b) ⟩
 + b - (+ a)
 ≡⟨ sym (⊖-to-- b a) ⟩
 b ℤ.⊖ a
 ∎ 
ℕ+-to-ℤ+ : (a b : ℕ) → + (a ℕ.+ b) ≡ + a ℤ.+ + b
ℕ+-to-ℤ+ a b = refl

open import Relation.Binary
open import Data.Nat.Properties.Simple 
open import Data.Nat.Properties
open DecTotalOrder ℕ.decTotalOrder using () renaming (trans to ≤-trans; antisym to ≤-antisym; refl to ≤-refl)
ℤ⊖-' : (a b : ℕ) → a ℕ.+ b ℤ.⊖ b ≡ ℤ.+ a
ℤ⊖-' a b rewrite ⊖-≥ {a ℕ.+ b} {b} (n≤m+n a b) = cong (λ x → + x) (m+n∸n≡m a b)
