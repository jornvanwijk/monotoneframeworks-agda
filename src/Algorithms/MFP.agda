import Level
open import MonotoneFramework
open import Monotonicity
open import LatticeTheory
open import Data.Bool hiding (_≟_)
open import Data.Vec as 𝕍 hiding (_∈_)
open import Data.List as 𝕃
open import Data.List.NonEmpty as 𝕃⁺
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Fin
open import Data.Nat hiding (_⊔_ ; _⊓_ ; _≟_)
open import Data.Product
open import Function
open import Induction.WellFounded
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Negation
open import Data.List.All hiding (lookup ; tabulate)
import Data.List.All as ListAll
open import Data.List.Any 
open import Data.Sum
import Data.Fin.Properties as Fin
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Util.Product
open import Data.List.Any.Properties
open import Function.Inverse using (Inverse)
open import Function.Equality using (_⟨$⟩_)
import Relation.Binary.List.Pointwise as Pointwise
open import Data.List.Any.Membership as Any∈   
open import Data.List.All.Properties


module Algorithms.MFP {a} (mf : MonotoneFramework a) where
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


module Simple where
  {-# TERMINATING #-}
  mfp : (x : V.ℂ) → (workList : List Edge) → V.ℂ 
  mfp x [] = x
  mfp x ((ℓ , ℓ′) ∷ workList) with 𝑓 ℓ x ⊑? lookup ℓ′ x 
  mfp x ((ℓ , ℓ′) ∷ workList) | yes p = mfp x workList
  mfp x ((ℓ , ℓ′) ∷ workList) | no ¬p = mfp (x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x) (outgoing F ℓ′ 𝕃.++ workList)

module WithTermination where 
  mfp : (x : V.ℂ) → Acc V._⊐_ x → (workList : List Edge) → V.ℂ 
  mfp x x₁ [] = x
  mfp x x₁ ((ℓ , ℓ′) ∷ workList) with 𝑓 ℓ x ⊑? lookup ℓ′ x 
  mfp x x₁ ((ℓ , ℓ′) ∷ workList) | yes p = mfp x x₁ workList
  mfp x (acc rs) ((ℓ , ℓ′) ∷ workList) | no ¬p = mfp x' (rs x' x⊏x') (outgoing F ℓ′ 𝕃.++ workList)
   where x' : V.ℂ 
         x' = x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x
         
         x⊑x' : x V.⊑ x'
         x⊑x' = ⊑-by-element L x ℓ′ (𝑓 ℓ x ⊔ lookup ℓ′ x) right-⊔-on-⊑

         x≠x' : ¬ x ≡ x'
         x≠x' x≡x' = contradiction
           (begin
           𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
           ≡⟨ sym (lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x)) ⟩
           lookup ℓ′ x'
           ≡⟨ sym (cong (lookup ℓ′) x≡x') ⟩
           lookup ℓ′ x
           ∎) ¬p
           
         x⊏x' : x V.⊏ x'
         x⊏x' = x⊑x' , x≠x'         

  mfp○ : V.ℂ
  mfp○ = mfp initial (V.⊐-isWellFounded initial) F
  
  mfp● : V.ℂ
  mfp● = tabulate 𝓕 ⊛ mfp○ 

   
  mfp-result : V.ℂ × V.ℂ
  mfp-result = (mfp○ , mfp●)
   



module ProvenWithTermination where
  open Membership-≡
  

  open import Data.FixedPoint.VectorFixedPoint mf
  open FixedPoint

  initial⊑fp : (y : FixedPoint) → initial V.⊑ fp y
  initial⊑fp y = ⊑-by-element' L initial (fp y) (λ i → begin
                                                       lookup i initial
                                                        ⊑⟨ ⊔-on-right-⊑ ⊑-reflexive ⟩
                                                        lookup i initial ⊔ ⨆ (𝕃.map (flip 𝑓 (fp y)) (predecessors F i))
                                                        ≡⟨ isFixedPoint y i  ⟩
                                                        lookup i (fp y)
                                                        ∎)

  mfp : 
    -- for all vectors x
       (x : V.ℂ)      
    -- that are below or equal to all other fixed points          
     → ((y : FixedPoint) → x V.⊑ fp y)    
    -- and of which all greater values are accessible
     → Acc V._⊐_ x                 
    -- and is above or equal to the initial value       
     → initial V.⊑ x  
    -- and for all work lists                   
     → (workList : List Edge)   
    -- that have all of their elements originating from the flow graph           
     → ((e : Edge) → e ∈ workList → e ∈ F) 
    -- and such that all two labels that form an edge in the flow graph are 
    -- either contained in the work list or the value at ℓ′ in x is bigger or equal to
    -- the transfer function applied over the value at ℓ in x.
     → ((ℓ ℓ′ : Label) → (ℓ , ℓ′) ∈ F → 
        ((ℓ , ℓ′) ∈ workList) ⊎ (lookup ℓ′ x ⊒ 𝓕 ℓ (lookup ℓ x))) 
    -- and such that for all ℓ′ the value at ℓ′ in x is less or equal to the maximal value 
    -- of the transfer function applied over all predecessors and the initial value at ℓ′.                                           
     → ((ℓ′ : Label) → lookup ℓ′ x ⊑ lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors F ℓ′)))
    -- there exists a fixed point, such that it is smaller than all other fixed points                        
     → Σ[ c ∈ FixedPoint ] ((y : FixedPoint) → fp c V.⊑ fp y)
  mfp x x⊑fp x₁ ι⊑x [] vf ⋄x⊒fx x⊑⨆f = record { fp = x ; isFixedPoint = x≡⨆f } , x⊑fp
    where
      x⊒fx : (ℓ ℓ′ : Label) → (ℓ , ℓ′) ∈ F → lookup ℓ′ x ⊒ 𝓕 ℓ (lookup ℓ x)
      x⊒fx ℓ ℓ′ p with ⋄x⊒fx ℓ ℓ′ p
      x⊒fx ℓ ℓ′ p | inj₁ ()
      x⊒fx ℓ ℓ′ p | inj₂ y = y
      
      x⊒⨆f : (ℓ′ : Label) → lookup ℓ′ x ⊒ ⨆ (𝕃.map (\ℓ → 𝑓 ℓ x) (predecessors F ℓ′))
      x⊒⨆f ℓ′ = x⊒⨆ (lookup ℓ′ x) (𝕃.map (\ℓ → 𝑓 ℓ x) (predecessors F ℓ′)) (ListAll.tabulate qq)
        where qq : {x₂ : ℂ} → x₂ ∈ 𝕃.map (λ ℓ → 𝑓 ℓ x) (predecessors F ℓ′) → lookup ℓ′ x ⊒ x₂
              qq {w} x₃ = let (a , b , c) = Inverse.from map-∈↔ ⟨$⟩ x₃
                              (z , r ) = predecessors-⊆′ F ℓ′ (a , b)
                          in  begin
                              w
                              ≡⟨ c ⟩
                              𝑓 (proj₁ (Inverse.from map-∈↔ ⟨$⟩ x₃)) x
                              ⊑⟨ x⊒fx z ℓ′ r ⟩
                              lookup ℓ′ x
                              ∎ 
      x≡⨆f : IsFixedPoint x
      x≡⨆f ℓ′ = sym (⊑-antisym (x⊑⨆f ℓ′) (⊔-on-right-⊒ (⊑-on-element L initial x ℓ′ ι⊑x) (x⊒⨆f ℓ′)))
                                               
  mfp x x⊑fp x₁ ι⊑x ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx x⊑⨆f with 𝑓 ℓ x ⊑? lookup ℓ′ x
  mfp x x⊑fp x₁ ι⊑x ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx x⊑⨆f | yes p = mfp x x⊑fp x₁ ι⊑x workList (λ e x₂ → vf e (there x₂)) ⋄x⊒fx' x⊑⨆f
    where 
      ⋄x⊒fx' : (l₃ l₄ : Label) → (l₃ , l₄) ∈ F → (l₃ , l₄) ∈ workList ⊎ (lookup l₄ x ⊒ 𝓕 l₃ (lookup l₃ x))
      ⋄x⊒fx' l₃ l₄ x₁ with ℓ Fin.≟ l₃ | ℓ′ Fin.≟ l₄ | ⋄x⊒fx l₃ l₄ x₁
      ⋄x⊒fx' l₃ l₄ x₁  | yes refl | yes refl | _ = inj₂ p
      ⋄x⊒fx' l₃ l₄ x₁  | no ¬p | q | inj₁ (here u) = contradiction (sym (proj₁ (≡-on-× u))) ¬p
      ⋄x⊒fx' l₃ l₄ x₁  | p | no ¬q | inj₁ (here u) = contradiction (sym (proj₂ (≡-on-× u))) ¬q
      ⋄x⊒fx' l₃ l₄ x₁  | p | q | inj₁ (there u) = inj₁ u
      ⋄x⊒fx' l₃ l₄ x₁  | p | q | inj₂ u = inj₂ u
  mfp x x⊑fp (acc rs) ι⊑x ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx x⊑⨆f | no ¬p = mfp x' x'⊑fp (rs x' x⊏x') ι⊑x' (outgoing F ℓ′ 𝕃.++ workList) (λ e x₁ →
    let r = Inverse.from (Data.List.Any.Properties.++↔ {xs = outgoing F ℓ′} {ys = workList}) ⟨$⟩ x₁
    in case r of (λ{ (inj₁ x₂) → outgoing-⊆ F ℓ′ x₂ ; (inj₂ y) → vf e (there y)})) ⋄x'⊒fx' x'⊑⨆f
    where
      x' : V.ℂ 
      x' = x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x
      
      x⊑x' : x V.⊑ x'
      x⊑x' = ⊑-by-element L x ℓ′ (𝑓 ℓ x ⊔ lookup ℓ′ x) right-⊔-on-⊑
                                                       
      x≠x' : ¬ x ≡ x'
      x≠x' x≡x' = contradiction
        (begin
          𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ sym (lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x)) ⟩
          lookup ℓ′ x'
          ≡⟨ sym (cong (lookup ℓ′) x≡x') ⟩
          lookup ℓ′ x
          ∎) ¬p
          
      x⊏x' : x V.⊏ x'
      x⊏x' = x⊑x' , x≠x'
                    
      currentEdgeExistsInFlow : (ℓ , ℓ′) ∈ F
      currentEdgeExistsInFlow = vf (ℓ , ℓ′) (here refl)
                                                  
      currentEdgeInPredecessors : ℓ ∈ predecessors F ℓ′
      currentEdgeInPredecessors = predecessors-∈ F (ℓ , ℓ′) currentEdgeExistsInFlow
                                                            
      open Reasoning
           
      ι⊑x' : initial V.⊑ x'
      ι⊑x' = V.⊑-trans ι⊑x x⊑x'  
           
      fx⊑fx′-pointwise : (z : Label) → 𝑓 z x ⊑ 𝑓 z x'
      fx⊑fx′-pointwise z with z Fin.≟ ℓ′
      fx⊑fx′-pointwise z | yes refl = begin
        𝓕 ℓ′ (lookup ℓ′ x) ⊔ 𝓕 ℓ′ (lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
        ≡⟨ cong (\i → 𝓕 ℓ′ (lookup ℓ′ x) ⊔ 𝓕 ℓ′ i) (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        𝓕 ℓ′ (lookup ℓ′ x) ⊔ 𝓕 ℓ′ (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ 𝓕-isMonotone ℓ′ (
           begin
           lookup ℓ′ x ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
           ≡⟨ sym (⊔-assoc _ _ _) ⟩
           (lookup ℓ′ x ⊔ 𝓕 ℓ (lookup ℓ x)) ⊔ lookup ℓ′ x
           ≡⟨ cong (_⊔ lookup ℓ′ x) (⊔-comm _ _) ⟩
           (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) ⊔ lookup ℓ′ x
           ≡⟨ ⊔-assoc _ _ _ ⟩
           𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x ⊔ lookup ℓ′ x
           ≡⟨ cong (_⊔_ (𝓕 ℓ (lookup ℓ x))) (⊔-idem _) ⟩
           𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
           ∎) ⟩ 
        𝓕 ℓ′ (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ cong (𝓕 ℓ′) (sym (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))) ⟩
        𝓕 ℓ′ (lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
        ∎
      fx⊑fx′-pointwise z | no z≠ℓ′ = begin
        𝓕 z (lookup z x) ⊔ 𝓕 z (lookup z (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
        ≡⟨ cong (\i → 𝓕 z (lookup z x) ⊔ 𝓕 z i) (lookup∘update′ z≠ℓ′ _ _) ⟩ 
        𝓕 z (lookup z x) ⊔ 𝓕 z (lookup z x)
        ≡⟨ ⊔-idem _ ⟩ 
        𝓕 z (lookup z x)
        ≡⟨ cong (𝓕 z) (sym (lookup∘update′ z≠ℓ′ _ _)) ⟩ 
        𝓕 z (lookup z (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
        ∎
          
      ⨆fx⊑⨆fx' : (ℓ′′ : Label) →  ⨆ (𝕃.map (flip 𝑓 x) (predecessors F ℓ′′)) ⊑ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′′))
      ⨆fx⊑⨆fx' ℓ′′ = ⨆⊑⨆-pointwise (𝕃.map (flip 𝑓 x) (predecessors F ℓ′′)) (𝕃.map (flip 𝑓 x') (predecessors F ℓ′′))
        (Pointwise.rec (λ {v} {v₁} v₂ → Pointwise.Rel _⊑_ (𝕃.map (flip 𝑓 x) v) (𝕃.map (flip 𝑓 x') v₁)) (λ {a} {b} {xs} {ys} {xs∼ys} x∼y x₂ → f {a} {b} {xs} {ys} {xs∼ys} x∼y x₂) Pointwise.[] (Pointwise.≡⇒Rel≡ (refl {_} {_} {predecessors F ℓ′′})))
        where f : {a : Label} {b : Label} {xs ys : List Label} {xs∼ys : Pointwise.Rel _≡_ xs ys} (x∼y : a ≡ b) → Pointwise.Rel _⊑_ (𝕃.map (flip 𝑓 x) xs) (𝕃.map (flip 𝑓 x') ys) →
                  Pointwise.Rel _⊑_ (flip 𝑓 x a ∷ 𝕃.map (flip 𝑓 x) xs) (flip 𝑓 x' b ∷ 𝕃.map (flip 𝑓 x') ys)
              f {a} {.a} refl x₁ = fx⊑fx′-pointwise a Pointwise.∷ x₁
      
      x'⊑⨆f : (ℓ′′ : Label) → lookup ℓ′′ x' ⊑ lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′′ ))
      x'⊑⨆f ℓ′′ with ℓ′′ Fin.≟ ℓ′
      x'⊑⨆f .ℓ′ | yes refl = begin
                             lookup ℓ′ x'
                             ≡⟨ lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x) ⟩
                             𝑓 ℓ x ⊔ lookup ℓ′ x
                             ⊑⟨ ⊔-on-left-⊑
                                (begin
                                𝑓 ℓ x
                                ⊑⟨ fx⊑fx′-pointwise _ ⟩
                                𝑓 ℓ x'
                                ⊑⟨ x⊑⨆x (𝑓 ℓ x') (𝕃.map (flip 𝑓 x') (predecessors F ℓ′)) (Inverse.to map-∈↔ ⟨$⟩ (ℓ , (currentEdgeInPredecessors , refl)) ) ⟩   
                                ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′))
                                ⊑⟨ right-⊔-on-⊑ ⟩
                                lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′))
                                ∎)
                                (begin
                                lookup ℓ′ x                             
                                ⊑⟨ x⊑⨆f ℓ′  ⟩
                                lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors F ℓ′))
                                ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′ initial)) ⊔-monotone-left (⨆fx⊑⨆fx' ℓ′) ⟩ 
                                lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′))
                                ∎) ⟩
                             lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′))
                             ∎ 
      x'⊑⨆f ℓ′′ | no ℓ′′≠ℓ′ = begin
                           lookup ℓ′′ x'
                           ≡⟨ lookup∘update′ ℓ′′≠ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x) ⟩
                           lookup ℓ′′ x
                           ⊑⟨ x⊑⨆f ℓ′′ ⟩
                           lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors F ℓ′′))
                           ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′′ initial)) ⊔-monotone-left (⨆fx⊑⨆fx' ℓ′′) ⟩
                           lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x') (predecessors F ℓ′′))
                           ∎ 
                            
      x'⊑fp : (y : FixedPoint) → x' V.⊑ fp y
      x'⊑fp y = V.begin
                x'
                V.≡⟨⟩
                x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x
                V.⊑⟨ ⊑-on-element' L x (fp y) ℓ′ (𝑓 ℓ x ⊔ lookup ℓ′ x) (x⊑fp y) (begin
                  𝑓 ℓ x ⊔ lookup ℓ′ x
                  ≡⟨⟩
                  𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x 
                  ⊑⟨ ⊔-on-⊑
                     (begin
                     𝓕 ℓ (lookup ℓ x)
                     ⊑⟨ 𝓕-isMonotone ℓ (⊑-on-element L x (fp y) ℓ (x⊑fp y)) ⟩
                     𝓕 ℓ (lookup ℓ (fp y))
                     ∎)
                     (begin
                     lookup ℓ′ x
                     ⊑⟨ ⊑-on-element L x (fp y) ℓ′ (x⊑fp y) ⟩
                     lookup ℓ′ (fp y)
                     ∎) ⟩ 
                  𝓕 ℓ (lookup ℓ (fp y)) ⊔ lookup ℓ′ (fp y)
                  ⊑⟨ right-⊔-on-⊑ ⟩
                  lookup ℓ′ initial ⊔ 𝓕 ℓ (lookup ℓ (fp y)) ⊔ lookup ℓ′ (fp y)
                  ≡⟨ sym (⊔-assoc _ _ _) ⟩
                  (lookup ℓ′ initial ⊔ 𝓕 ℓ (lookup ℓ (fp y))) ⊔ lookup ℓ′ (fp y)
                  ≡⟨  fixed⇒reductive (fp y) (isFixedPoint y) ℓ ℓ′ currentEdgeExistsInFlow  ⟩
                  lookup ℓ′ (fp y)
                  ∎) ⟩
                fp y
                V.∎
                  
      ⋄x'⊒fx' : (l₃ l₄ : Label) → (l₃ , l₄) ∈ F → (l₃ , l₄) ∈ outgoing F ℓ′ 𝕃.++  workList ⊎ (lookup l₄ x' ⊒ 𝓕 l₃ (lookup l₃ x'))
      ⋄x'⊒fx' l₃ l₄ x₁ with ⋄x⊒fx l₃ l₄ x₁
      ⋄x'⊒fx' l₃ l₄ x₁ | inj₁ (there u) = inj₁ (++ʳ (outgoing F ℓ′) u)
      ⋄x'⊒fx' .ℓ .ℓ′ x₁ | inj₁ (here refl) with ℓ Fin.≟ ℓ′
      ⋄x'⊒fx' .ℓ .ℓ′ x₁ | inj₁ (here refl) | yes refl = inj₁ (++ˡ (outgoing-∈ F (ℓ , ℓ) currentEdgeExistsInFlow)) 
      ⋄x'⊒fx' .ℓ .ℓ′ x₁ | inj₁ (here refl) | no ℓ≠ℓ′ = inj₂
        (begin
          𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ i) (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ cong (\i → 𝓕 ℓ i ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) (lookup∘update′ ℓ≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ sym (⊔-assoc _ _ _) ⟩
          (𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 ℓ (lookup ℓ x)) ⊔ lookup ℓ′ x
          ≡⟨ cong (\i → i ⊔ lookup ℓ′ x) (⊔-idem (𝓕 ℓ (lookup ℓ x))) ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ sym (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩ 
          lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ∎)
      ⋄x'⊒fx' l₃ l₄ x₁ | inj₂ u with l₃ Fin.≟ ℓ′ | l₄ Fin.≟ ℓ′
      ⋄x'⊒fx' .ℓ′ .ℓ′ x₁ | inj₂ u | yes refl | yes refl = inj₁ (++ˡ (outgoing-∈ F (ℓ′ , ℓ′) x₁))
      ⋄x'⊒fx' .ℓ′ l₄ x₁ | inj₂ u | yes refl | no q = inj₁ (++ˡ (outgoing-∈ F (ℓ′ , l₄) x₁)) -- er moet dan een ℓ′′ zijn zodat, ℓ′ ,ℓ′′ ∈ Outgoing F ℓ′,
      ⋄x'⊒fx' l₃ .ℓ′ x₁ | inj₂ u | no p | yes refl = inj₂ (begin
        𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ cong (\i → 𝓕 l₃ i ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) (lookup∘update′ p x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        𝓕 l₃ (lookup l₃ x) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ cong (\i → 𝓕 l₃ (lookup l₃ x) ⊔ i) (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        𝓕 l₃ (lookup l₃ x) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
        ≡⟨ sym (⊔-assoc _ _ _) ⟨ trans ⟩ cong (_⊔ lookup ℓ′ x) (⊔-comm (𝓕 l₃ (lookup l₃ x)) (𝓕 ℓ (lookup ℓ x))) ⟨ trans ⟩ ⊔-assoc _ _ _ ⟩
        𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 l₃ (lookup l₃ x) ⊔ lookup ℓ′ x
        ≡⟨ cong (_⊔_ (𝓕 ℓ (lookup ℓ x))) u  ⟩
        𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
        ≡⟨ sym (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ∎)
      ⋄x'⊒fx' l₃ l₄ x₁ | inj₂ u | no p | no q = inj₂ (begin
        𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ cong (\i → 𝓕 l₃ i ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) (lookup∘update′ p x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        𝓕 l₃ (lookup l₃ x) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ≡⟨ cong (\i → 𝓕 l₃ (lookup l₃ x) ⊔ i) (lookup∘update′ q x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        𝓕 l₃ (lookup l₃ x) ⊔ lookup l₄ x
        ≡⟨ u ⟩
        lookup l₄ x
        ≡⟨ sym (lookup∘update′ q x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
        lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
        ∎)

  maximal-fixed-point : Σ[ c ∈ FixedPoint ] ((y : FixedPoint) → fp c V.⊑ fp y)
  maximal-fixed-point = mfp initial initial⊑fp (V.⊐-isWellFounded initial) V.⊑-reflexive F (λ e x → x) (λ ℓ ℓ′ x → inj₁ x) (λ ℓ′ → ⊔-on-right-⊑ ⊑-reflexive)

  
  mfp○ : V.ℂ
  mfp○ = fp (proj₁ maximal-fixed-point) 
  
  mfp● : V.ℂ
  mfp● = tabulate 𝓕 ⊛ mfp○ 

  mfp-result : V.ℂ × V.ℂ
  mfp-result = (mfp○ , mfp●)
