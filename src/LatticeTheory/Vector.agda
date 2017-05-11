import Level

module LatticeTheory.Vector {a : Level.Level} where

import Algebra.FunctionProperties
open import Algebra.Structures
open import LatticeTheory.Core
open import LatticeTheory.Product
open import LatticeTheory.Unit
open import Data.Empty renaming (⊥ to Empty-⊥)
open import Data.Nat hiding (_⊔_ ; _⊓_ ; _≟_)
open import Data.Product
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Product.N-ary
open import Data.Unit hiding (_≟_)
open import Data.Vec
open import Data.Vec.N-ary
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Consequences.Core
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Util.Function
open import LatticeTheory.Core
open ≡-Reasoning
import Function.Inverse as I
open I hiding (_∘_ ; sym)
import Function.Equality as E
open E hiding (cong; _∘_)


N-ary-×ᴸ : BoundedSemiLattice a → (n : ℕ) → BoundedSemiLattice a
N-ary-×ᴸ L zero = Unitᴸ
N-ary-×ᴸ L (suc zero) = L
N-ary-×ᴸ L (suc n) = L ×ᴸ (N-ary-×ᴸ L n)

module Vec-×-Inverse {L : BoundedSemiLattice a} where
    
    to-tuple : {n : ℕ} → (open BoundedSemiLattice L) -> Vec ℂ n -> BoundedSemiLattice.ℂ (N-ary-×ᴸ L n) --Vecᴸ' n ?
    to-tuple {zero} x = Level.lift tt    
    to-tuple {(suc zero)} (x ∷ []) = x
    to-tuple {(suc (suc n))} (x ∷ x₁) = x , (to-tuple {(suc n)} x₁)

    to-vec : {n : ℕ} → (open BoundedSemiLattice L) → BoundedSemiLattice.ℂ (N-ary-×ᴸ L n) → Vec ℂ n  --N-ary-×ᴸ n ?
    to-vec {zero} (Level.lift lower) = []
    to-vec {suc zero}  x = Data.Vec.[ x ]
    to-vec {suc (suc n)}  (x , xs) = x ∷ to-vec xs
    right-inverse-of : {n : ℕ} → (open BoundedSemiLattice L) → (x : BoundedSemiLattice.ℂ (N-ary-×ᴸ L n)) -> to-tuple {n} (to-vec {n} x) ≡ x
    right-inverse-of {zero} x = refl
    right-inverse-of {suc zero} x = refl
    right-inverse-of {suc (suc n)} (x , xs) = cong₂ _,_ refl (right-inverse-of {suc n} xs)

    left-inverse-of : {n : ℕ} → (open BoundedSemiLattice L) → (x : Vec ℂ n) -> to-vec {n} (to-tuple {n} x) ≡ x
    left-inverse-of {zero} [] = refl
    left-inverse-of {suc zero} (x ∷ []) = refl
    left-inverse-of {suc (suc n)} (x ∷ xs) = cong₂ _∷_ refl (left-inverse-of {suc n} xs)
  
    inverse : {n : ℕ} → (open BoundedSemiLattice L) → Vec ℂ n ↔ BoundedSemiLattice.ℂ (N-ary-×ᴸ L n)
    inverse {n} = record
                  { to = →-to-⟶ (to-tuple {n})
                  ; from = →-to-⟶ (to-vec {n})
                  ; inverse-of = record
                    { left-inverse-of = left-inverse-of {n}
                    ; right-inverse-of = right-inverse-of {n}
                    }
                  }
                  
{-# DISPLAY Vec-×-Inverse.to-vec x = x #-}
{-# DISPLAY Vec-×-Inverse.to-tuple x = x #-}
open Vec-×-Inverse using () renaming (inverse to Vecᴸ↔N-ary-×ᴸ) public
open import LatticeTheory.ByBijection --hiding (module Properties)

Vecᴸ : BoundedSemiLattice a → (n : ℕ) -> BoundedSemiLattice a
Vecᴸ L n = fromBijectionᴸ (Vec (BoundedSemiLattice.ℂ L) n) (N-ary-×ᴸ L n) Vecᴸ↔N-ary-×ᴸ


open import Data.Fin --(A : Set a) (L : BoundedSemiLattice b) (open BoundedSemiLattice L) (inv : A ↔ ℂ)
module _ (L : BoundedSemiLattice a) where
  private
    module L where
      open BoundedSemiLattice L public
      open BoundedSemiLattice.Reasoning L public

  open import Data.Fin
  open import Data.Vec

  open ≡-Reasoning


  --theorem: tail is gelijk aan een vector van een lagere n.
  -- to (from x ⊔ from y)  ≡    .. Vec.⊔ ..
  
  ⊔-replicate : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → x ⊔ y ≡ (replicate L._⊔_ ⊛ x ⊛ y)
  ⊔-replicate {zero} [] [] = refl
  ⊔-replicate {suc zero} (x ∷ []) (x₂ ∷ []) = refl
  ⊔-replicate {suc (suc n)} (x ∷ x₁) (x₂ ∷ y) with LatticeTheory.ByBijection.Properties.to (Vec L.ℂ (suc (suc n))) (N-ary-×ᴸ L (suc (suc n))) ( Vecᴸ↔N-ary-×ᴸ {L} {suc (suc n)}) (x ∷ x₁)
  ⊔-replicate {suc (suc n)} (x ∷ x₁) (x₂ ∷ y) | proj₃ , proj₄ = cong (x L.⊔ x₂ ∷_) (⊔-replicate {suc n} x₁ y)

  lookup-⊔ : {n : ℕ} → (ℓ : Fin n) → (x y : Vec (L.ℂ) n) → lookup ℓ x L.⊔ lookup ℓ y ≡ lookup ℓ (BoundedSemiLattice._⊔_ (Vecᴸ L n) x y)
  lookup-⊔ {zero} () x y
  lookup-⊔ {suc zero} zero (x ∷ []) (y ∷ []) = refl
  lookup-⊔ {suc zero} (suc ()) x y
  lookup-⊔ {suc (suc n)} zero (x ∷ xs) (y ∷ ys) = refl
  lookup-⊔ {suc (suc n)} (suc ℓ) (x ∷ xs) (y ∷ ys) = lookup-⊔ {suc n} ℓ xs ys 


  ⊑-by-element : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x : ℂ) → (i : Fin n) → (v : L.ℂ) → (lookup i x) L.⊑ v → x ⊑ (x [ i ]≔ v)
  ⊑-by-element {zero} x () v x₁
  ⊑-by-element {suc zero} (x ∷ []) zero v x₂ = cong (\x → x ∷ []) x₂
  ⊑-by-element {suc zero} x (suc ()) v x₁
  ⊑-by-element {suc (suc n)} (x ∷ x₁) zero v x₂ = trans (cong (_∷_ (x L.⊔ v)) (V.⊔-idem x₁)) (cong (\x → x ∷ x₁) x₂) 
    where
      module V where
        open BoundedSemiLattice (Vecᴸ L (suc n)) public
  ⊑-by-element {suc (suc n)} (x ∷ x₁) (suc i) v x₂ = trans (cong (_∷_ (x L.⊔ x)) (⊑-by-element {suc n} x₁ i v x₂)) (cong (\y → y ∷ x₁ [ i ]≔ v) (L.⊔-idem x) )
    where
      module V where
        open BoundedSemiLattice (Vecᴸ L (suc n)) public


  ⊑-by-element' : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → ((i : Fin n) → lookup i x L.⊑ lookup i y) → x ⊑ y
  ⊑-by-element' {zero} [] [] x₁ = refl
  ⊑-by-element' {suc zero} (x ∷ []) (y ∷ []) i = cong (_∷ []) (i (# 0))
  ⊑-by-element' {suc (suc n)} (x ∷ xs) (y ∷ ys) i = cong₂ _∷_ (i (# 0)) (⊑-by-element' {suc n} xs ys (λ j → i (suc j)))


  ⊑-on-element' : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → (i : Fin n) → (v : L.ℂ) → x ⊑ y → v L.⊑ (lookup i y) → (x [ i ]≔ v) ⊑ y
  ⊑-on-element' {zero} x [] () _ _ _
  ⊑-on-element' {suc zero} (x ∷ []) (x₂ ∷ []) zero v p q = cong (_∷ []) q
  ⊑-on-element' {suc zero} (x ∷ x₁) y (suc ()) v p q
  ⊑-on-element' {suc (suc n)} (x ∷ x₁) (x₂ ∷ y) zero v p x₃ = cong₂ _∷_ x₃ (cong tail p)
  ⊑-on-element' {suc (suc n)} (x ∷ x₁) (x₂ ∷ y) (suc i) v p x₃ = cong₂ _∷_ (cong head p) (⊑-on-element' {suc n} x₁ y i v (cong tail p) x₃)

  -- lookup-mono 
  ⊑-on-element : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → (l : Fin n) →  x ⊑ y → lookup l x L.⊑ lookup l y
  ⊑-on-element {zero} x y () x₁
  ⊑-on-element {suc zero} (x ∷ []) (y ∷ []) zero x₂ = cong head x₂
  ⊑-on-element {suc zero} x y (suc ()) x₁
  ⊑-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) zero x₁ = cong head x₁
  ⊑-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) (suc l) x₁ = ⊑-on-element {suc n} xs ys l (cong tail x₁)
  
  ⊒-on-element : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → (l : Fin n) →  x ⊒ y → lookup l x L.⊒ lookup l y
  ⊒-on-element {zero} x y () x₁
  ⊒-on-element {suc zero} (x ∷ []) (y ∷ []) zero x₂ = cong head x₂
  ⊒-on-element {suc zero} x y (suc ()) x₁
  ⊒-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) zero x₁ = cong head x₁
  ⊒-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) (suc l) x₁ = ⊒-on-element {suc n} xs ys l (cong tail x₁)
  
  ≡-on-element : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → (l : Fin n) →  x ≡ y → lookup l x ≡ lookup l y
  ≡-on-element {zero} x y () x₁
  ≡-on-element {suc zero} (x ∷ []) (y ∷ []) zero x₂ = cong head x₂
  ≡-on-element {suc zero} x y (suc ()) x₁
  ≡-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) zero x₁ = cong head x₁
  ≡-on-element {suc (suc n)} (x ∷ xs) (y ∷ ys) (suc l) x₁ = ≡-on-element {suc n} xs ys l (cong tail x₁)
  


  lookup-⊥ : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (ℓ : Fin n) → lookup ℓ ⊥ ≡ L.⊥
  lookup-⊥ {zero} ()  -- 
  lookup-⊥ {suc zero} zero = refl
  lookup-⊥ {suc zero} (suc ℓ) = lookup-⊥ {zero} ℓ
  lookup-⊥ {suc (suc n)} zero = refl
  lookup-⊥ {suc (suc n)} (suc ℓ) = lookup-⊥ ℓ

  
  lookup-⊥-isMinimal : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (ℓ : Fin n) → (x : L.ℂ) → lookup ℓ ⊥ L.⊑ x
  lookup-⊥-isMinimal {n} ℓ x = L.begin
                               lookup ℓ ⊥
                               L.≡⟨ lookup-⊥ ℓ ⟩
                               BoundedSemiLattice.⊥ L
                               L.⊑⟨ BoundedSemiLattice.⊥-isMinimal L _ ⟩
                               x L.∎
    where open BoundedSemiLattice (Vecᴸ L n)


  x⊑y⇒⨆xs⊑⨆ys : {n : ℕ} → (open BoundedSemiLattice (Vecᴸ L n)) → (x y : ℂ) → x ⊑ y → L.⨆ (toList x) L.⊑ L.⨆ (toList y)
  x⊑y⇒⨆xs⊑⨆ys {zero} [] [] refl = BoundedSemiLattice.⊔-idem L _
  x⊑y⇒⨆xs⊑⨆ys {suc zero} (x ∷ []) (y ∷ []) x₂ = L.begin
                                   (x L.⊔ L.⊥) L.⊔ y L.⊔ L.⊥
                                   L.≡⟨ L.⊔-cong₂ ((L.⊔-comm _ _) ⟨ trans ⟩ L.⊥-isMinimal x ) ((L.⊔-comm _ _) ⟨ trans ⟩ L.⊥-isMinimal y) ⟩
                                   x L.⊔ y
                                   L.≡⟨ cong head x₂ ⟩
                                   y
                                   L.≡⟨ sym (trans (L.⊔-comm _ _) (L.⊥-isMinimal y)) ⟩
                                   y L.⊔ L.⊥
                                   L.∎ 
  x⊑y⇒⨆xs⊑⨆ys {suc (suc n)} (x ∷ x₁) (x₂ ∷ y) x₃ = 
    L.begin
      (x L.⊔ L.⨆ (toList x₁)) L.⊔ x₂ L.⊔ L.⨆ (toList y)
    L.≡⟨ L.⊔-over-⊔ ⟩
     (x L.⊔ x₂) L.⊔ L.⨆ (toList x₁) L.⊔ L.⨆ (toList y)
    L.≡⟨ L.⊔-cong₂ (cong head x₃) (x⊑y⇒⨆xs⊑⨆ys {suc n} x₁ y (cong tail x₃)) ⟩
     x₂ L.⊔ L.⨆ (toList y)
    L.∎ 
