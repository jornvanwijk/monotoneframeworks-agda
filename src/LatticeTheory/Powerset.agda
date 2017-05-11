open import Data.Nat hiding (_⊔_)
module LatticeTheory.Powerset where

module _ (n : ℕ) where
  open import LatticeTheory.Core
  open import LatticeTheory.Bool
  open import LatticeTheory.Vector

  {- Subset n = Vec Bool   is a lattice because    Bool,∨,∧,false is a complete lattice and a vector of a complete lattice is also a complete lattice -} 
  𝓟ᴸ : BoundedSemiLattice _
  𝓟ᴸ = Vecᴸ Mayᴸ n

  𝓟ᴸ-by-inclusion : BoundedSemiLattice _
  𝓟ᴸ-by-inclusion = 𝓟ᴸ

  𝓟ᴸ-by-exclusion : BoundedSemiLattice _
  𝓟ᴸ-by-exclusion = Vecᴸ Mustᴸ n


  open BoundedSemiLattice 𝓟ᴸ
  open import Data.Bool
  open import Data.Fin
  open import Data.Vec hiding (_∈_)
  open import Data.Fin.Subset
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality    
  open import Data.Vec.Properties
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Data.Bool
  open import Data.Bool.Properties
  open import Function.Equivalence hiding (sym)
  open import Data.Product
  open import Function.Equality hiding (cong)
  open import Relation.Nullary.Decidable
  open ≡-Reasoning
  open import Function.Inverse hiding (sym)
  
  ⊑-to-setFin∈ : {x : Fin n} → {a b : ℂ} → a ⊑ b → x ∈ a → x ∈ b
  ⊑-to-setFin∈ {x} {a} {b} a⊑b x∈a = Inverse.from []=↔lookup ⟨$⟩ (begin lookup x b
                                      ≡⟨ sym (⊑-on-element Boolᴸ {n} a b x a⊑b) ⟩
                                      lookup x a ∨ lookup x b
                                      ≡⟨ cong (_∨ lookup x b) (Inverse.to []=↔lookup ⟨$⟩ x∈a) ⟩
                                      true
                                      ∎)

  
  module Instantiated {a} {A : Set a} (fin↔ : A ↔ Fin n) where
    open import Util.Subset
    open Containment fin↔
    open import Data.Sum
    ⊑-to-set∈ : {x : A} → {a b : ℂ} → a ⊑ b → x set∈ a → x set∈ b
    ⊑-to-set∈ {x} a⊑b x-set∈-a = ⊑-to-setFin∈ a⊑b (set∈-≡ refl x-set∈-a)

    ⊔-to-∪ : {a b : ℂ} → a ⊔ b ≡ a ∪ b
    ⊔-to-∪ = ⊔-replicate Boolᴸ _ _

    ⊔-to-set∈ : {x : A} → {a b : ℂ} → x set∈ a → x set∈ a ⊔ b
    ⊔-to-set∈ {x} x-set∈-a = ⊑-to-set∈ left-⊔-on-⊑ x-set∈-a 
