
module Utilities where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product hiding (map)


-- membership

open import Relation.Binary
DecEq : Set → Set
DecEq X = Decidable {A = X} _≡_

isProp : Set → Set
isProp X = {x y : X} → x ≡ y

infix 4 _∈_

data  _∈_ {X : Set} (y : X) : List X → Set where
  here  : ∀ {xs x} → y ≡ x → y ∈ x ∷ xs
  there : ∀ {x xs} → y ∈ xs → y ∈ x ∷ xs

-- duplicates

data Dup {X : Set} : List X → Set where
  duphere  : ∀ {x} {xs : List X} → x ∈ xs → Dup (x ∷ xs)
  dupthere : ∀ {x} {xs : List X} → Dup xs → Dup (x ∷ xs)

data Dup' {X : Set} : List X → Set where
  duphere  : ∀ {x} {xs : List X} → x ∈ xs → Dup' (x ∷ xs)

∈map : {X Y : Set}{x : X}{xs : List X}(f : X → Y) → x ∈ xs → f x ∈ map f xs
∈map f (here p) = here (cong f p)
∈map f (there p) = there (∈map f p)

Dupmap : {X Y : Set}(f : X → Y)(xs : List X) → Dup xs → Dup (map f xs)
Dupmap f .(x ∷ xs) (duphere {x} {xs} p) = duphere (∈map f p)
Dupmap f .(x ∷ xs) (dupthere {x} {xs} p) = dupthere (Dupmap f xs p)



_++R_ : {X : Set} → List X → List X → List X
[] ++R ys = ys
(x ∷ xs) ++R ys = xs ++R (x ∷ ys)

dup++R2 : {X : Set}(xs : List X){ys : List X} → Dup ys → Dup (xs ++R ys)
dup++R2 [] d = d
dup++R2 (x ∷ xs) d = dup++R2 xs (dupthere d)

∈++R : {X : Set}{xs ys : List X}{x : X} → x ∈ xs → x ∈ ys → Dup (xs ++R ys)
∈++R {xs = x ∷ xs}(here refl) p = dup++R2 xs (duphere p) 
∈++R (there i) p = ∈++R i (there p)

dup++R : {X : Set}{xs ys : List X} → Dup xs → Dup (xs ++R ys)
dup++R (duphere d) = ∈++R d (here refl)
dup++R (dupthere d) = dup++R d


open import Data.Nat
sucInj : {n m : ℕ} → suc n ≡ suc m → n ≡ m
sucInj refl = refl

lengthDup : {X : Set}{xs : List X} → Dup xs → ℕ
lengthDup (duphere d) = zero
lengthDup (dupthere d) = suc (lengthDup d)


open import Relation.Nullary
open import Data.Empty
open import Data.Nat

remove : ∀ {X : Set} {x : X} → (xs : List X) → x ∈ xs → List X
remove .(_ ∷ xs) (here {xs} refl)     = xs
remove .(x' ∷ xs) (there {x'} {xs} y) = x' ∷ (remove xs y)

∈remove : ∀ {X : Set} {xs : List X} {x y : X} →
          ¬ y ≡ x → (p : x ∈ xs) → y ∈ xs → y ∈ remove xs p
∈remove ¬eq (here refl) (here refl) = ⊥-elim (¬eq refl)
∈remove ¬eq (here refl) (there q) = q
∈remove ¬eq (there p) (here refl) = here refl
∈remove ¬eq (there p) (there q) = there (∈remove ¬eq p q)

length-remove : ∀ {X : Set} {n} {xs : List X} {x : X} → (p : x ∈ xs) → 
                length xs ≡ suc n → length (remove xs p) ≡ n  
length-remove (here refl) refl = refl
length-remove {xs = x' ∷ []} (there ()) p
length-remove (there (here refl)) refl = refl
length-remove {X} {.(suc (length xs))} {x' ∷ x ∷ xs} (there (there y)) refl = 
  cong suc (length-remove {xs = x ∷ xs} (there y) refl)
