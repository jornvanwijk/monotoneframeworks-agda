module Util.Fin-product where

open import Data.Nat as ℕ
open import Data.Fin as 𝔽
open import Data.Fin.Properties as 𝔽-prop hiding (setoid)


-- <m → < m + n
finl : ∀ {m} n → Fin m → Fin (m ℕ.+ n)
finl = inject+
{-# DISPLAY inject+ = finl #-}

-- <n → < m + n
finr : ∀ {n} m → Fin n → Fin (m ℕ.+ n)
finr zero x = x
finr (suc n) x = suc (finr n x)

data FinPlus (m n : ℕ) : Fin (m ℕ.+ n) -> Set where
  IsFinl : (i : Fin m) -> FinPlus m n (finl n i)
  IsFinr : (i : Fin n) -> FinPlus m n (finr m i)

finPlus : (m n : ℕ) → (i : Fin (m ℕ.+ n)) → FinPlus m n i
finPlus zero n i = IsFinr i
finPlus (suc m) n zero = IsFinl zero
finPlus (suc m) n (suc i) with finPlus m n i
finPlus (suc m) n (suc .(finl n i)) | IsFinl i = IsFinl (suc i)
finPlus (suc m) n (suc .(finr m i)) | IsFinr i = IsFinr i

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
disjoint : (m n : ℕ) → (i : Fin (m ℕ.+ n)) → (a : FinPlus m n i) → (Σ[ j ∈ Fin m ] i ≡ finl n j) ⊎ Σ[ j ∈ Fin n ] i ≡ finr m j
disjoint m n .(finl n i) (IsFinl i) = inj₁ (i , refl)
disjoint m n .(finr m i) (IsFinr i) = inj₂ (i , refl)

-- <m × <n  →  <m*n
fpair : {m n : ℕ} -> Fin m -> Fin n -> Fin (m * n)
fpair {m} {n} zero j = finl _ j
fpair {m} {n} (suc i) j = finr n (fpair i j)

{- 
fpairdisjoint : {m n : ℕ} → (i : Fin m) → (j : Fin n) → fpair i j ≡ finl _ j ⊎ fpair i j ≡ finr n (fpair i j)
fpairdisjoint = ?
-}
open import Data.Empty

data FTimes {m n : ℕ} : Fin (m * n) -> Set where
  IsFPair : (i : Fin m) -> (j : Fin n) -> FTimes (fpair i j)

finTimes : (m n : ℕ) → (i : Fin (m * n)) → FTimes {m} {n} i
finTimes zero n ()
finTimes (suc m) n i with finPlus n (m * n) i
finTimes (suc m) n .(finl (m * n) i) | IsFinl i = IsFPair zero i
finTimes (suc m) n .(finr n i) | IsFinr i with finTimes m n i
finTimes (suc m) n .(finr n (fpair i j)) | IsFinr .(fpair i j) | (IsFPair i j) = IsFPair (suc i) j





open import Data.Product
open import Function.Inverse
open import Function.Equality hiding (cong) renaming (setoid to _Π-setoid_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Function.Injection

fsInj : {m : ℕ} → Injective {B = setoid (Fin (suc m))} (→-to-⟶ suc)
fsInj refl = refl 

finlInj : {m n : ℕ} → Injective {B = setoid (Fin (m ℕ.+ n))} (→-to-⟶ (finl {m} n)) 
finlInj {.(suc _)} {n} {zero} {zero} refl = refl
finlInj {.(suc _)} {n} {zero} {suc y} ()
finlInj {.(suc _)} {n} {suc x} {zero} ()
finlInj {.(suc _)} {n} {suc x} {suc y} x₂ = cong suc (finlInj (fsInj x₂))

finrInj : {m n : ℕ} → Injective {B = setoid (Fin (m ℕ.+ n))} (→-to-⟶ (finr {n} m))
finrInj {zero} {n} {x} {y} p = p
finrInj {suc m} {n} {x} {y} x₁ = finrInj {m} (fsInj x₁)

{-
fpairInj : {m n : ℕ} → (j : Fin n) → Injective {B = setoid (Fin (m * n))} (→-to-⟶ (λ x → fpair {m} {n} x j))
fpairInj j {zero} {zero} p = refl
fpairInj j {zero} {suc y} p = {!!}
fpairInj j {suc x} {y} p = {!!}


fpairInj1 : {m n : ℕ} -> (i i' : Fin n) -> (j : Fin m) -> fpair i j ≡ fpair i' j -> i ≡ i'
fpairInj1 zero zero j p = refl
fpairInj1 {m} {n} (zero {n₁}) (suc {n₂} i') j p with finPlus m (n₁ * m) (finr m (fpair i' j)) | finPlus m (n₁ * m) (finl (n₁ * m) j)
fpairInj1 {m} {.(suc zero)} (zero {zero}) (suc {.zero} ()) j p | q | r
fpairInj1 {m} {.(suc (suc n))} (zero {suc n}) (suc {.(suc n)} i') j p | q | r = {!q!}
fpairInj1 (suc i) zero j p = {!!}
fpairInj1 {m} {n} (suc i) (suc i') j p = cong suc (fpairInj1 i i' j (finrInj {m} p))


fpairInj2 : {m n : ℕ} -> (i : Fin n) -> (j j' : Fin m) -> fpair i j ≡ fpair i j' -> j ≡ j'
fpairInj2 zero j j' p = finlInj p
fpairInj2 {m} (suc {n} i) j j' p = fpairInj2 i j j' (finrInj {m} p)
-}

module _ where
--  open Inverse
  open _InverseOf_

  to : ∀ {m n} → Fin (m * n) → (Fin m) × (Fin n)
  to {m} {n} i with finTimes m n i
  to {m} {n} .(fpair i j) | IsFPair i j = i , j

  from : ∀ {m n} → (Fin m) × (Fin n) → Fin (m * n)
  from {m} {n} (a , b) = fpair a b

  open import Relation.Nullary
  open import Util.Product
  postulate 
    toCorrect : ∀ {m n} -> (x : Fin (m * n)) -> (i : Fin m) → (j : Fin n)  -> x ≡ fpair i j -> to x ≡ (i , j)
  {-
  toCorrect {m} {n} x i j x₁ with finTimes m n x
  toCorrect {m} {n} .(fpair i j) i₁ j₁ x₁ | IsFPair i j with i 𝔽-prop.≟ i₁ | j 𝔽-prop.≟ j₁
  toCorrect {m} {n} .(fpair i j) .i j₁ x₁ | IsFPair i j | (yes refl) | r = ≡×⇒≡ (refl , (fpairInj2 i j j₁ x₁))
  toCorrect {m} {n} .(fpair i j) i₁ .j x₁ | IsFPair i j | (no ¬p) | (yes refl) = ≡×⇒≡ ((fpairInj1 i i₁ j x₁) , refl)
  toCorrect {m} {n} .(fpair i j) i₁ j₁ x₁ | IsFPair i j | (no ¬p) | (no ¬p₁) = {!!}
  -}
  
  id1 : ∀ {m n} -> (p : (Fin m) × (Fin n)) -> to (from p) ≡ p
  id1 {m} {n} (x , x₁) = toCorrect (fpair x x₁) x x₁ refl
    
  id2 : ∀ {m n} -> (i : (Fin (m * n))) -> from {m} {n} (to i) ≡ i
  id2 {m} {n} i with finTimes m n i
  id2 .(fpair i j) | IsFPair i j = refl

  fin*↔fin× : (m n : ℕ) → Fin (m * n) ↔ ((Fin m) × (Fin n))
  Inverse.to (fin*↔fin× m n) = →-to-⟶ to
  Inverse.from (fin*↔fin× m n) = →-to-⟶ from
  left-inverse-of (Inverse.inverse-of (fin*↔fin× m n)) = id2 {m} {n}
  right-inverse-of (Inverse.inverse-of (fin*↔fin× m n)) = id1

  open Function.Inverse
  fin×↔fin* : (m n : ℕ) → ((Fin m) × (Fin n)) ↔ Fin (m * n)
  fin×↔fin* m n = Function.Inverse.sym (fin*↔fin× m n)

{-
fooCorrect : ∀ {m n} -> (x : Fin (m * n))
  -> (i : Fin n) -> (j : Fin m) ->
  x ≡ fpair j i ->
  foo x  (j , i)
fooCorrect {m} {n} x i j p with finTimes m n x
fooCorrect {m} {n} .(fpair i j) i₁ j₁ p | IsFPair i j = {!fpairInj1 {?} {m} i j₁ j!}



{- with fpairInj1 {n} {m} {!!} {!fp!} {!i₁!} p
... | q = {!fpairInj1 {n} {m} ? ? ? p!} -}


-}
