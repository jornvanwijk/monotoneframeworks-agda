open import Relation.Binary.PropositionalEquality
open import LatticeTheory
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.List as 𝕃
open import Function
open import MonotoneFramework
open import Function.Inverse
open import Data.List.Any.Membership
open import Function.Equality hiding (flip)

module Data.FixedPoint.VectorFixedPoint {a} (mf : MonotoneFramework a) where

  open MonotoneFramework.MonotoneFramework mf
  open import Data.Graph n
  open LatticeTheory.BoundedSemiLattice L 
  open Reasoning
  private
    module V where
      open LatticeTheory.BoundedSemiLattice (Vecᴸ L n) public
      open BoundedSemiLattice.Reasoning (Vecᴸ L n) public

  open import Data.Fin.Dec
  open import Data.Fin.Properties as FinP
  open import Data.List.Any
  open Membership-≡
  

  IsFixedPoint : Vec ℂ n → Set a
  IsFixedPoint c = (ℓ′ : Fin n) → lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 c) (predecessors F ℓ′)) ≡ lookup ℓ′ c
           
  record FixedPoint : Set a where
    field
      fp : V.ℂ
      isFixedPoint : IsFixedPoint fp
  open FixedPoint

  -- afgezwakte eis
  -- want eigenlijk: (ℓ′ : Label) → ⨆ (𝕃.map (flip 𝑓 c) (lookup ℓ′ (predecessors F))) ⊑ lookup ℓ′ c
  IsReductivePoint : V.ℂ → Set a
  IsReductivePoint c = (ℓ ℓ′ : Label) → (ℓ , ℓ′) ∈ F → lookup ℓ′ initial ⊔ 𝑓 ℓ c ⊑ lookup ℓ′ c
                                                                         
  record ReductivePoint : Set a where
    field
      rp : V.ℂ
      isReductivePoint : IsReductivePoint rp
  open ReductivePoint

  fixed⇒reductive : (c : V.ℂ) → IsFixedPoint c → IsReductivePoint c
  fixed⇒reductive c p ℓ ℓ′ x =
    begin
    lookup ℓ′ initial ⊔  𝑓 ℓ c
    ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′ initial)) ⊔-monotone-left (x⊑⨆x (𝑓 ℓ c) (𝕃.map (λ l₃ → 𝑓 l₃ c) (predecessors F ℓ′)) lemma) ⟩
    lookup ℓ′ initial ⊔ ⨆ (𝕃.map (λ l₃ → 𝑓 l₃ c) (predecessors F ℓ′))
    ≡⟨ p ℓ′ ⟩
    lookup ℓ′ c
    ∎
    where lemma : 𝓕 ℓ (lookup ℓ c) ∈ 𝕃.map (λ l₃ → (𝓕 l₃ (lookup l₃ c))) (predecessors F ℓ′)
          lemma = Inverse.to map-∈↔ ⟨$⟩ (ℓ , (Inverse.to map-∈↔ ⟨$⟩ (((ℓ , ℓ′)) , ((incoming-∈ F (ℓ , ℓ′) x) , refl)) , refl))
