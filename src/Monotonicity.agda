module Monotonicity where
import Level
open import Relation.Binary using (Rel)



BiMonotone₂ : ∀{ℓ₁ ℓ₂ a₁ a₂} -> {ℂ₁ : Set a₁} -> {ℂ₂ : Set a₂}  -> Rel ℂ₁ ℓ₁ -> Rel ℂ₂ ℓ₂ -> (f : ℂ₁ → ℂ₁ -> ℂ₂) -> Set (a₁ Level.⊔ ℓ₁ Level.⊔ ℓ₂)
BiMonotone₂ _⊑₁_ _⊑₂_ f = ∀{x y z w} -> x ⊑₁ y → z ⊑₁ w -> f x z ⊑₂ f y w

BiMonotone : ∀{ℓ a} -> {ℂ : Set a}  -> Rel ℂ ℓ -> (f : ℂ → ℂ -> ℂ) -> Set (a Level.⊔ ℓ)
BiMonotone _⊑_ f = BiMonotone₂ _⊑_ _⊑_ f


Monotone₂ : ∀{ℓ₁ ℓ₂ a₁ a₂} -> {ℂ₁ : Set a₁} -> {ℂ₂ : Set a₂}  -> Rel ℂ₁ ℓ₁ -> Rel ℂ₂ ℓ₂ -> (f : ℂ₁ -> ℂ₂) -> Set (a₁ Level.⊔ ℓ₁ Level.⊔ ℓ₂)
Monotone₂ _⊑₁_ _⊑₂_ f = ∀{x y} -> x ⊑₁ y -> f x ⊑₂ f y

Monotone : ∀{a ℓ} -> {ℂ : Set a} -> Rel ℂ ℓ -> (f : ℂ -> ℂ) -> Set (a Level.⊔ ℓ)
Monotone _⊑_ f = Monotone₂ _⊑_ _⊑_ f


{-
open import Relation.Nullary
open import Data.Product
open import Data.Sum
Atomic : ∀{a ℓ} -> {ℂ : Set a} -> Rel ℂ ℓ -> (f : ℂ -> ℂ) -> Set (a Level.⊔ ℓ)
Atomic {ℂ = ℂ} _⊑_ f = (a : ℂ) → ¬ ( Σ[ b ∈ ℂ ] a ⊑ b × b ⊑ f a)

monotonicity-preserves-atomicity : ∀{a ℓ} -> {ℂ : Set a} -> (_⊑_ : Rel ℂ ℓ) -> (f : ℂ -> ℂ) → Monotone _⊑_ f → Atomic _⊑_ f
monotonicity-preserves-atomicity _⊑_ f x a₁ (proj₃ , proj₄ , proj₅) = {!!}
-}





open import Util.Listable
open import Relation.Binary
open import Relation.Nullary
open import Function
open import Data.List
open import Data.List.All renaming (all to all?)
open import Relation.Nullary.Implication

module _ {a} {ℓ} {ℂ : Set a} (f : ℂ -> ℂ) (_⊑_ : Rel ℂ ℓ) (_⊑?_ : Decidable _⊑_) (ls : Listable ℂ) where
  decidable-monotonicity : Dec (Monotone _⊑_ f)
  decidable-monotonicity with all? (λ x → all? (λ y → x ⊑? y →-dec f x ⊑? f y) (Listable.all ls)) (Listable.all ls)
  decidable-monotonicity | yes p = yes (λ{ {x} {y} q → (lookup (lookup p (Listable.complete ls x)) (Listable.complete ls y)) q })
  decidable-monotonicity | no ¬p = no (λ ⊑-isMonotone → ¬p (tabulate (λ {x} x₂ → tabulate (λ {y} x₃ x⊑y → ⊑-isMonotone x⊑y)))) 



{-
open import Data.Nat as ℕ
module _ {n : ℕ} where
  open import Data.Fin as 𝔽
  open import Relation.Nullary.Decidable
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Util.Listable
  open import Data.Nat.Properties
  f-mono : Fin n → Fin n
  f-mono zero = zero
  f-mono (suc x) = zero
  
  
  f-nonmono : Fin n → Fin n
  f-nonmono zero = zero
  f-nonmono (suc x) = zero

  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable

  exa : Dec (Monotone 𝔽._≤_ f-mono)
  exa = decidable-monotonicity f-mono 𝔽._≤_ 𝔽._≤?_ fin-listable
  
  f-mono-zero : ∀{m} (i : Fin n) → f-mono i ≡ {!zero!}
  f-mono-zero i = {!!}

  explicit : Monotone 𝔽._≤_ f-mono
  explicit {x} {y} p with f-mono x | inspect f-mono x
  explicit {x} {y} p | zero | r = z≤n
  explicit {x} {y} p | suc q | Reveal_·_is_.[ eq ] = {!p!}

  explicit' : Monotone 𝔽._≤_ f-mono
  explicit' {x} {y} p with  f-mono x | inspect f-mono x
  explicit' {x} {y} p | .(f-mono x) | Reveal_·_is_.[ refl ] = {!!}
  
  q : { _ : True (exa) } → Monotone 𝔽._≤_ f-mono
  q { p } = toWitness p
  
  qqq : { _ : From-yes (exa) } → Monotone 𝔽._≤_ f-mono
  qqq { p } = {!from-yes!}

  open import Data.Sum
  open import Data.Unit
  instance 
    alldec : ∀{p} → {P : Set p} → (d : Dec P) → True d ⊎ False d
    alldec d with d
    alldec d | yes p₁ = inj₁ tt
    alldec d | no ¬p = inj₂ tt

  instance
    fromWitness' : ∀ {p} {P : Set p} {Q : Dec P} → P → True Q
    fromWitness' {Q = yes p} = const _
    fromWitness' {Q = no ¬p} = ¬p
   
  dd : ∀{p} → {P : Set p} → (d : Dec P) → True d → P
  dd d x = {!mWitness x!}

  it : ∀ {a} {A : Set a} {{_ : A}} → A
  it {{x}} = x


  z : Monotone 𝔽._≤_ f-mono
  z {x} {y} = q {_}
  
  _F<?_ : ∀ {n} → (a : Fin n) → (b : Fin n) → Dec (a 𝔽.< b)
  a F<? b = {!toℕ a <? toℕ b!} --

  qq : { _ : True (decidable-monotonicity f-mono 𝔽._<_ _F<?_ fin-listable) } → Monotone 𝔽._<_ f-mono
  qq {p} = toWitness p

  _F≥_ : Rel (Fin n) Level.zero
  _F≥_ = flip 𝔽._≤_

 -- {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ 
  flip? : ∀{a b ℓ} → {A : Set a} {B : Set b} → {_●_ : REL A B ℓ} → Decidable _●_ → Decidable (flip _●_)
  flip? ●? x y = ●? y x

  _F≥?_ : (a : Fin n) → (b : Fin n) → Dec (a F≥ b)
  _F≥?_ = flip? 𝔽._≤?_
  
  r : { _ : True (decidable-monotonicity f-mono _F≥_ _F≥?_ fin-listable) } → Monotone _F≥_ f-mono
  r {p} = toWitness p
  
--  x <- xs ; y <- ys   als x⊑y;  kijken of ook f x ⊑ f y   (als ergens het niet geldt; dan nee; anders ja)


--∀{x y} -> x ⊑ y -> f x ⊑ f y


{-

  f ≟ g with all? (λ x → f x L.≟ g x) (Listable.all ls)
  f ≟ g | yes p = yes (fun-ext (λ x → lookup p (Listable.complete ls x)))
  f ≟ g | no ¬p = no (λ x → ¬p (tabulate (λ {y} p → cong (_$ y) x )))
  -}



--f x y ⊑ g x y    ⇔?   f (x , y) ⊑ g (x , y)  
-}
