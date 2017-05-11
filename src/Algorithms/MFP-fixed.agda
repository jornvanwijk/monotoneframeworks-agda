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

module Algorithms.MFP-fixed {a n} (mf : MonotoneFramework a n) where
open MonotoneFramework.MonotoneFramework mf
open import Data.Graph n
open BoundedSemiLattice L 
open Reasoning
private
  module V where
    open BoundedSemiLattice (Vecᴸ L n) public
    open BoundedSemiLattice.Reasoning (Vecᴸ L n) public

open import Data.Fin.Dec
open import Data.Fin.Properties as FinP

initial : V.ℂ
initial = tabulate (λ i →  if ⌊ Data.List.Any.any (FinP._≟ i) (𝕃⁺.toList E) ⌋ then ι else ⊥)

{-

we willen een datastructuur zodat:


datastructuur No duplicates list: 
  []
  x : []
  x : y : []    (zodat x ≠ y)
                (en de garantie dat domein van x en y eindig; of wel, domein is lattice.



een datastructuur (FiniteStack)  zodat:

  []
  push x : []
  push y : push x : []   (zodat x ≠ y)
  pop : push y : push x : []   (zodat   # pops <= # push)



dan kunnen we een fixpoint functie schrijven op:
  (FiniteStack , Vec ℂ n)
die telkens iets van de stack haalt, een update op de vector doet, en eventueel nieuwe dingen op de stack zet.

(uit definitie fix point volgt dat de FiniteStack wel leeg moet zijn; anders kunnen we nog een keer de functie toepassen.)
(als de FinitiStack leeg is, dan moet dus de gehele worklist zijn uitgevoerd
Als we de garantie hebben dat alle edges in de worklist gezeten hebben, dan ..



--------------------------------------------------


Stel we hebben een functie 𝑔 die berekent een fixpoint ω ∈ (L × L).
Kunnen we dan wat zeggen over: proj₁ ω en proj₂ ω

We weten dat:  IsFixedPoint (ω₁ , ω₂)

dus: Σ[ ω′ ∈ L ] IsFixedPoint (ω′ , ω₂)


If L × L has a fixed point, then there exists a function such that either domein has a fixed point.
isFixedPoint 𝑔 (ω₁ , ω₂) → IsFixedPoint (λ x → proj₁ ∘ g $ (x , ω₂)) ω₁ × IsFixedPoint (λ x → proj₂ ∘ 𝑔 $ (ω₁ , x)) ω₂ 





voor onze specifieke 𝑔 weten we dat:
  - Voor elke fixed point moet gelden dat ω₁ ≡ []

Het is voor ons belangrijk om te onthouden dat:
  𝑓 x = 𝑔 (W , x)
we weten dat 𝑔 een fixed point (ω₁ , ω₂) geeft en dat ω₁ ooit een keer W was.  ( de gehele worklist )










stel we hebben een functie

𝑘 : ℕ → ℕ
𝑘 i = if i > 5 then i - 1 else i

𝑙 : ℕ → ℕ
𝑙 i = if i > 5 then i - 2 else i

stel ω = solve 𝑘 α
omdat 𝑘 monotoon is, en 𝑘 een vast verschil heeft moeten voor alle Δ: ω ≤ α-(1 * Δ) ≤ α gelden:    isFixedPoint 𝑘 α-(1 * Δ)
Als 𝑘 10 een fix point is en waarde 5 heeft, dan hebben 𝑘 9, 𝑘 8, 𝑘 7, 𝑘 6, 𝑘 5 ook een fixed point
Als k 2 een fix point is en waarde 2 heeft, dan bestaat er geen Δ zodat 2 ≤ 2 - Δ ≤ 2 zodat Δ ≠ 2.








-}


        












{-
module Simple where
  {-# TERMINATING #-}
  mfp : (x : V.ℂ) → (workList : List Edge) → V.ℂ 
  mfp x [] = x
  mfp x ((ℓ , ℓ′) ∷ workList) with 𝑓 ℓ x ⊑? lookup ℓ′ x 
  mfp x ((ℓ , ℓ′) ∷ workList) | yes p = mfp x workList
  mfp x ((ℓ , ℓ′) ∷ workList) | no ¬p = mfp (x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x) (outgoing F ℓ′ 𝕃.++ workList)

module WithTermation where 
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

  -- Helaas missen we nu bewijs dat het een fixed point is.
  mfp○ : V.ℂ
  mfp○ = mfp initial (V.⊐-isWellFounded initial) F
  
  mfp● : V.ℂ
  mfp● = tabulate 𝓕 ⊛ mfp○ 

   
  mfp-result : V.ℂ × V.ℂ
  mfp-result = (mfp○ , mfp●)
   



module ProvenWithTermination where
  open Membership-≡
  
  IsFixedPoint : V.ℂ → Set a
  IsFixedPoint c = (ℓ′ : Label) → lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 c) (predecessors F ℓ′)) ≡ lookup ℓ′ c
           
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

  initial⊑fp : (y : FixedPoint) → initial V.⊑ fp y
  initial⊑fp y = ⊑-by-element' L initial (fp y) (λ i → begin
                                                       lookup i initial
                                                        ⊑⟨ ⊔-on-right-⊑ ⊑-reflexive ⟩
                                                        lookup i initial ⊔ ⨆ (𝕃.map (flip 𝑓 (fp y)) (predecessors F i))
                                                        ≡⟨ isFixedPoint y i  ⟩
                                                        lookup i (fp y)
                                                        ∎)


  transfer-mfp' : (x : V.ℂ)
                → ((y : FixedPoint) → x V.⊑ fp y)    -- we stay below fixed point
                → Acc V._⊐_ x                        -- we terminate
                → (workList : List Edge) 
                → ((e : Edge) → e ∈ workList → e ∈ F) -- we stay true to the program flow
                → ((ℓ ℓ′ : Label) → (ℓ , ℓ′) ∈ F → ((ℓ , ℓ′) ∈ workList) ⊎ (lookup ℓ′ x ⊒ 𝓕 ℓ (lookup ℓ x))) -- everything not in the worklist must be above its predecessors
                → initial V.⊑ x -- we stay above initial values
                → ((ℓ′ : Label) → lookup ℓ′ x ⊑ lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors F ℓ′))) -- we stay true to the information flow, and do not add irrelevant information
                → Σ[ c ∈ FixedPoint ] ((y : FixedPoint) → fp c V.⊑ fp y)
  transfer-mfp' x x⊑fp x₁ [] vf ⋄x⊒fx ι⊑x x⊑⨆f = record { fp = x ; isFixedPoint = x≡⨆f } , x⊑fp
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
                                               
  transfer-mfp' x x⊑fp x₁ ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx ι⊑x x⊑⨆f with 𝑓 ℓ x ⊑? lookup ℓ′ x
  transfer-mfp' x x⊑fp x₁ ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx ι⊑x x⊑⨆f | yes p = transfer-mfp' x x⊑fp x₁ workList (λ e x₂ → vf e (there x₂)) ⋄x⊒fx' ι⊑x x⊑⨆f
    where 
      ⋄x⊒fx' : (l₃ l₄ : Label) → (l₃ , l₄) ∈ F → (l₃ , l₄) ∈ workList ⊎ (lookup l₄ x ⊒ 𝓕 l₃ (lookup l₃ x))
      ⋄x⊒fx' l₃ l₄ x₁ with ℓ Fin.≟ l₃ | ℓ′ Fin.≟ l₄ | ⋄x⊒fx l₃ l₄ x₁
      ⋄x⊒fx' l₃ l₄ x₁  | yes refl | yes refl | _ = inj₂ p
      ⋄x⊒fx' l₃ l₄ x₁  | no ¬p | q | inj₁ (here u) = contradiction (sym (proj₁ (≡-on-× u))) ¬p
      ⋄x⊒fx' l₃ l₄ x₁  | p | no ¬q | inj₁ (here u) = contradiction (sym (proj₂ (≡-on-× u))) ¬q
      ⋄x⊒fx' l₃ l₄ x₁  | p | q | inj₁ (there u) = inj₁ u
      ⋄x⊒fx' l₃ l₄ x₁  | p | q | inj₂ u = inj₂ u
  transfer-mfp' x x⊑fp (acc rs) ((ℓ , ℓ′) ∷ workList) vf ⋄x⊒fx ι⊑x x⊑⨆f | no ¬p = transfer-mfp' x' x'⊑fp (rs x' x⊏x') (outgoing F ℓ′ 𝕃.++ workList) (λ e x₁ →
    let r = Inverse.from (Data.List.Any.Properties.++↔ {xs = outgoing F ℓ′} {ys = workList}) ⟨$⟩ x₁
    in case r of (λ{ (inj₁ x₂) → outgoing-⊆ F ℓ′ x₂ ; (inj₂ y) → vf e (there y)})) ⋄x'⊒fx' ι⊑x' x'⊑⨆f
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

  maximal-fixed-point' : Σ[ c ∈ FixedPoint ] ((y : FixedPoint) → fp c V.⊑ fp y)
  maximal-fixed-point' = transfer-mfp' initial initial⊑fp (V.⊐-isWellFounded initial) F (λ e x → x) (λ ℓ ℓ′ x → inj₁ x) V.⊑-reflexive (λ ℓ′ → ⊔-on-right-⊑ ⊑-reflexive)
-}
