open import Relation.Binary.PropositionalEquality
open import LatticeTheory
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.List as 𝕃
open import Function
open import ExtendedFramework
open import Function.Inverse
open import Data.List.Any.Membership
open import Function.Equality hiding (flip)
import Level
open import Data.Nat hiding (_⊔_)

module Data.FixedPoint.VectorFlowFixedPoint {a} (mf : ExtendedFramework a) where


  open ExtendedFramework.ExtendedFramework mf
  open import Data.Graph n
  open BoundedSemiLattice L 

  open import Data.Fin.Dec
  open import Data.Fin.Properties as FinP
  open import Data.List.Any
  open Membership-≡ renaming (_∈_ to _list∈_)
  open import Data.List.All using (All)

  open ProductEncoding
  open import Util.Subset
  open Containment {Level.zero} {n * n} {Fin n × Fin n} (ℕ×ℕ↔ℕ n) 
  open Instantiated (n * n) (ℕ×ℕ↔ℕ n)
  private
    module V where
      open BoundedSemiLattice (Vecᴸ L n) public
      open BoundedSemiLattice.Reasoning (Vecᴸ L n) public
    module F where
      open BoundedSemiLattice Fᴸ public
      open BoundedSemiLattice.Reasoning Fᴸ public
  
  IsFixedPoint : CFG → V.ℂ → Set a
  IsFixedPoint F c = ((ℓ′ : Label) → (lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 c) (predecessors (set-to-list F) ℓ′)) ≡ lookup ℓ′ c ))
                     × F ≡ initial-F F.⊔ F.⨆ (𝕃.map (λ ℓ → next ℓ (lookup ℓ c)) (Data.Vec.toList (allFin n)))
                                     
           
  record FixedPoint (F : CFG) : Set a where
    field
      fp : V.ℂ
      isFixedPoint : IsFixedPoint F fp
  open FixedPoint

  IsReductivePoint : CFG → V.ℂ → Set a
  IsReductivePoint F c = (ℓ ℓ′ : Label) → (ℓ , ℓ′) set∈ F → lookup ℓ′ initial ⊔ 𝑓 ℓ c ⊑ lookup ℓ′ c -- 
                                                                         
  record ReductivePoint (F : CFG) : Set a where
    field
      rp : V.ℂ
      isReductivePoint : IsReductivePoint F rp
  open ReductivePoint
       
  open BoundedSemiLattice.Reasoning L
  open import Data.List.Any.Membership as Any∈   

                                          
  fixed⇒reductive : (F : CFG) → (c : V.ℂ) → IsFixedPoint F c → IsReductivePoint F c
  fixed⇒reductive F c x ℓ ℓ′ x₁ = begin
                                  lookup ℓ′ initial ⊔  𝑓 ℓ c
                                  ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′ initial)) ⊔-monotone-left (x⊑⨆x (𝑓 ℓ c) (𝕃.map (flip 𝑓 c) (predecessors (set-to-list F) ℓ′)) lemma) ⟩
                                  lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 c) (predecessors (set-to-list F) ℓ′))
                                  ≡⟨ proj₁ x ℓ′ ⟩ 
                                  lookup ℓ′ c
                                  ∎
    where lemma : 𝓕 ℓ (lookup ℓ c) list∈ (𝕃.map (flip 𝑓 c) (predecessors (set-to-list F) ℓ′))
          lemma = Inverse.to map-∈↔ ⟨$⟩ (ℓ , (Inverse.to map-∈↔ ⟨$⟩ ((ℓ , ℓ′) , ((incoming-∈ (set-to-list F) (ℓ , ℓ′) (set∈-to-list∈ x₁)) , refl)) , refl)) 
