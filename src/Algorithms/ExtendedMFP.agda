import Level
import Relation.Binary.List.Pointwise as Pointwise
open import LatticeTheory
open import Data.Bool
open import Data.Empty renaming (⊥ to Empty-⊥)
open import Data.Fin
open import Data.Fin.Dec
open import Data.Fin.Properties as FinP
open import Data.Fin.Subset renaming (⊥ to ∅)
open import Data.List as 𝕃
open import Data.List.All renaming (tabulate to tabulate-all) using ()
open import Data.List.All.Properties
open import Data.List.Any
open import Data.List.Any.Membership as AnyMembership
open import Data.List.Any.Properties
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Data.Vec.Properties
open import ExtendedFramework
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence)
open import Function.Inverse using (_↔_ ; Inverse)
open import Induction.WellFounded
open import Monotonicity
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Implication
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Util.List
open import Util.Product
open import Util.Subset
open import Util.Sum
open Membership-≡ renaming (_∈_ to _list∈_)
module Algorithms.ExtendedMFP {a} (mf : ExtendedFramework.ExtendedFramework a) where
  open ExtendedFramework.ExtendedFramework mf
  open import Data.FixedPoint.VectorFlowFixedPoint mf
  open ReductivePoint
  open FixedPoint
  open BoundedSemiLattice L
  open Reasoning
  open ProductEncoding
  open Containment {Level.zero} {n * n} {Fin n × Fin n} (ℕ×ℕ↔ℕ n)
  open Instantiated (n * n) (ℕ×ℕ↔ℕ n)
  open import Data.Graph n
  private
    module V where
      open BoundedSemiLattice (Vecᴸ L n) public
      open BoundedSemiLattice.Reasoning (Vecᴸ L n) public
    module F where
      open BoundedSemiLattice Fᴸ public
      open BoundedSemiLattice.Reasoning Fᴸ public
      
  acc-≡ : ∀{ℓ} → { ℂ : Set ℓ } {x y : ℂ} → {_⊑_ : Rel ℂ ℓ} → x ≡ y → Acc _⊑_ x → Acc _⊑_ y
  acc-≡ refl x₂ = x₂
  
  module Standard where
    {-# TERMINATING #-}
    mfp-extended : 
       -- for all vectors x
          (x : V.ℂ)
       -- and for all work lists
        → (workList : List (Label × Label))
       -- and for all control flow graphs
        → (F : CFG)
       -- there exists a control flow graph F̂ such that we obtain an x.
        → Σ[ F̂ ∈ CFG ] V.ℂ
    mfp-extended x [] F = F , x
    mfp-extended x ((ℓ , ℓ′) ∷ workList) F = case-nonemptyworklist (𝑓 ℓ x ⊑? lookup ℓ′ x)
     where
      v = 𝑓 ℓ x ⊔ lookup ℓ′ x
      F′ = F F.⊔ next ℓ′ v  
      F′⊒F : F′ F.⊒ F
      F′⊒F = F.⊔-on-right-⊑ F.⊑-reflexive  
      x′ = x [ ℓ′ ]≔ v
      case-nonemptyworklist : Dec (𝑓 ℓ x ⊑ lookup ℓ′ x) → Σ[ F̂ ∈ CFG ] V.ℂ
      case-nonemptyworklist (yes p) = mfp-extended x workList F
      case-nonemptyworklist (no ¬p) = mfp-extended x′ (set-to-list (F′ Util.Subset.- F) 𝕃.++ outgoing (set-to-list F) ℓ′  𝕃.++ workList) F′
  
    mfp : Σ[ F̂ ∈ CFG ] V.ℂ
    mfp = mfp-extended initial (set-to-list initial-F) initial-F


  module WithTermination where
    mfp-extended : 
       -- for all vectors x
          (x : V.ℂ)
       -- that are above or equal to the initial value       
        → Acc V._⊐_ x
       -- and for all work lists
        → (workList : List (Label × Label))
       -- and for all control flow graphs
        → (F : CFG)
       -- and of which all greater values are accessible
        → Acc F._⊐_ F
       -- there exists a control flow graph F̂ such that we obtain an x.
        → Σ[ F̂ ∈ CFG ] V.ℂ
    mfp-extended x rs [] F ts = F , x
    mfp-extended x rs ((ℓ , ℓ′) ∷ workList) F ts = case-nonemptyworklist (𝑓 ℓ x ⊑? lookup ℓ′ x) rs ts
     where
      v = 𝑓 ℓ x ⊔ lookup ℓ′ x
      F′ = F F.⊔ next ℓ′ v  
      F′⊒F : F′ F.⊒ F
      F′⊒F = F.⊔-on-right-⊑ F.⊑-reflexive  
      case-nonemptyworklist : Dec (𝑓 ℓ x ⊑ lookup ℓ′ x) → Acc V._⊐_ x → Acc F._⊐_ F → Σ[ F̂ ∈ CFG ] V.ℂ
      case-nonemptyworklist (yes p) rs ts = mfp-extended x rs workList F ts
      case-nonemptyworklist (no ¬p) (acc rs) ts = mfp-extended x′ (rs x′ x⊏x′) (set-to-list (F′ Util.Subset.- F) 𝕃.++ outgoing (set-to-list F) ℓ′  𝕃.++ workList) F′ (F-acc (F′ F.⊑? F) ts) 
       where
        F⊑F′ : F F.⊑ F′
        F⊑F′ = F.⊔-on-right-⊑ F.⊑-reflexive
        F-acc : Dec (F′ F.⊑ F) → Acc F._⊐_ F → Acc F._⊐_ F′
        F-acc (no ¬F′⊑F) (acc ts) = ts F′ (F.⊔-on-right-⊑ F.⊑-reflexive , (λ x₁ → ⊥-elim (¬F′⊑F (F.≡⇒⊑ (sym x₁)))))
        F-acc (yes F′⊑F) ts = acc-≡ (F.⊑-antisym F⊑F′ F′⊑F) ts
        x′ = x [ ℓ′ ]≔ v
        x⊑x′ : x V.⊑ x′
        x⊑x′ = ⊑-by-element L x ℓ′ (𝑓 ℓ x ⊔ lookup ℓ′ x) right-⊔-on-⊑
        x≠x′ : ¬ x ≡ x′
        x≠x′ x≡x′ = contradiction (
          begin
            𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
              ≡⟨ sym (lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x)) ⟩
              lookup ℓ′ x′
              ≡⟨ sym (cong (lookup ℓ′) x≡x′) ⟩
              lookup ℓ′ x
          ∎) ¬p
        x⊏x′ : x V.⊏ x′ 
        x⊏x′ = x⊑x′ , x≠x′

    mfp : Σ[ F̂ ∈ CFG ] V.ℂ
    mfp =
      mfp-extended
        initial
        (V.⊐-isWellFounded initial)
        (set-to-list initial-F)
        initial-F
        (F.⊐-isWellFounded initial-F)


  module ProvenWithTermination where
    -- Given any control flow graph F and any fixpoint y, we show that the initial point is less than the fix point.
    initial⊑fp : (F : CFG) → (y : FixedPoint F) → initial V.⊑ fp y
    initial⊑fp F y = ⊑-by-element' L initial (fp y) (λ i → begin
                                                       lookup i initial
                                                        ⊑⟨ ⊔-on-right-⊑ ⊑-reflexive ⟩
                                                        lookup i initial ⊔ ⨆ (𝕃.map (flip 𝑓 (fp y)) (predecessors (set-to-list F) i))
                                                        ≡⟨ proj₁ (isFixedPoint y) i ⟩
                                                        lookup i (fp y)
                                                        ∎)
 
    mfp-extended : 
       -- for all vectors x
          (x : V.ℂ)
       -- that are above or equal to the initial value       
        → initial V.⊑ x  
       -- and of which all greater values are accessible
        → Acc V._⊐_ x
       -- and for all work lists
        → (workList : List (Label × Label))
       -- and for all control flow graphs
        → (F : CFG)
       -- that are above or equal to the initial control flow graph
        → initial-F F.⊑ F
       -- and of which all greater values are accessible
        → Acc F._⊐_ F
       -- such that x is less or equal to any fixedpoint y for any F̂ that is greater or equal to F.
        → ((F̂ : CFG) → F̂ F.⊒ F → (y : FixedPoint F̂) → x V.⊑ fp y)
       -- and such that anything that is in the worklist originated from the flow graph  
        → ((ℓ ℓ′ : Label) → (ℓ , ℓ′) list∈ workList → (ℓ , ℓ′) set∈ F)
       -- and such that everything not in the worklist is above its predecessors
        → ((ℓ ℓ′ : Label) → (ℓ , ℓ′) set∈ F → ¬ (ℓ , ℓ′) list∈ workList → lookup ℓ′ x ⊒ 𝓕 ℓ (lookup ℓ x))
       -- and such that F contains all new control flow added by the next function for the current value.
        → ((ℓ : Label) → F F.⊒ next ℓ (lookup ℓ x))
       -- and such that for all ℓ′ the value at ℓ′ in x is less or equal to the maximal value 
       -- of the transfer function applied over all predecessors of ℓ′ using the current flow and the initial value at ℓ′.      
        → ((ℓ′ : Label) → lookup ℓ′ x ⊑ lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors (set-to-list F) ℓ′)))
       -- and such that the control flow graph remains true to the control flow graph defined by unification of the next function on all labels.
        → F F.⊑ initial-F F.⊔ F.⨆ (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) (Data.Vec.toList (allFin n)))
       -- there exists a control flow graph F̂ such that x is a fixed point, and all other fixed points under F̂ are bigger or equal to x.
        → Σ[ F̂ ∈ CFG ] Σ[ x ∈ FixedPoint F̂ ] ((y : FixedPoint F̂) → fp x V.⊑ fp y)
    mfp-extended x ι⊑x rs [] F ιF⊑F ts x⊑fp ∈worklist-⇒-∈F ◇x⊒fx ◇F⊒next x⊑⨆f F⊑⨆F = F , ( record { fp = x ; isFixedPoint = x≡⨆f }) , (x⊑fp F F.⊑-reflexive)
     where
       x⊒fx : (ℓ ℓ′ : Label) → (ℓ , ℓ′) set∈ F → lookup ℓ′ x ⊒ 𝓕 ℓ (lookup ℓ x)
       x⊒fx ℓ ℓ′ p = ◇x⊒fx ℓ ℓ′ p (λ{()})
       
       x⊒⨆f : (ℓ′ : Label) → lookup ℓ′ x ⊒ ⨆ (𝕃.map (\ℓ → 𝑓 ℓ x) (predecessors (set-to-list F) ℓ′)) 
       x⊒⨆f ℓ′ = x⊒⨆ (lookup ℓ′ x) (𝕃.map (\ℓ → 𝑓 ℓ x) (predecessors (set-to-list F) ℓ′)) (Data.List.All.tabulate qq)
        where qq : {x′ : ℂ} → x′ list∈ 𝕃.map (λ ℓ → 𝑓 ℓ x) (predecessors (set-to-list F) ℓ′) → (lookup ℓ′ x) ⊒ x′
              qq {x′} x′-list∈-map = let (a , b , c) = Inverse.from map-∈↔ ⟨$⟩ x′-list∈-map
                                         (z , r ) = predecessors-⊆′ (set-to-list F) ℓ′ (a , b)
                                    in begin
                                        x′
                                        ≡⟨ c ⟩
                                        𝑓 (proj₁ (Inverse.from map-∈↔ ⟨$⟩ x′-list∈-map)) x
                                        ⊑⟨ x⊒fx (proj₁ (Inverse.from map-∈↔ ⟨$⟩ x′-list∈-map)) ℓ′ (list∈-to-set∈ r) ⟩
                                        lookup ℓ′ x
                                        ∎

       F⊒⨆F : F F.⊒ initial-F F.⊔ F.⨆ (𝕃.map (λ ℓ → next ℓ (lookup ℓ x)) (toList (allFin n)))
       F⊒⨆F = F.⊔-on-right-⊒ ιF⊑F (F.x⊒⨆ F (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) (toList (allFin n))) (tabulate-all (λ {x} x₂ → case Inverse.from map-∈↔ ⟨$⟩ x₂ of (λ{ (ℓ′′ , proj₄ , proj₅) → F.⊑-trans (F.≡⇒⊑ proj₅) (◇F⊒next ℓ′′)}))))

       F≡⨆F : F ≡ initial-F F.⊔ F.⨆ (𝕃.map (λ ℓ → next ℓ (lookup ℓ x)) (Data.Vec.toList (allFin n)))
       F≡⨆F = F.⊑-antisym F⊑⨆F F⊒⨆F 
       
       x≡⨆f : IsFixedPoint F x
       x≡⨆f = (λ ℓ′ → sym (⊑-antisym (x⊑⨆f ℓ′) (⊔-on-right-⊒ (⊑-on-element L initial x ℓ′ ι⊑x) (x⊒⨆f ℓ′)))) , F≡⨆F
    mfp-extended x ι⊑x rs ((ℓ , ℓ′) ∷ workList) F ιF⊑F ts x⊑fp ∈worklist-⇒-∈F ⋄x⊒fx F⊒next x⊑⨆f F⊑⨆F = case-nonemptyworklist (𝑓 ℓ x ⊑? lookup ℓ′ x) rs ts
     where
      v = 𝑓 ℓ x ⊔ lookup ℓ′ x
      F′ = F F.⊔ next ℓ′ v  
      F′⊒F : F′ F.⊒ F
      F′⊒F = F.⊔-on-right-⊑ F.⊑-reflexive  
      currentEdgeExistsInFlow : (ℓ , ℓ′) set∈ F
      currentEdgeExistsInFlow = ∈worklist-⇒-∈F ℓ ℓ′ (here refl)
      currentEdgeInPredecessors : ℓ list∈ predecessors (set-to-list F) ℓ′
      currentEdgeInPredecessors = predecessors-∈ (set-to-list F) (ℓ , ℓ′) (set∈-to-list∈ currentEdgeExistsInFlow)
      currentEdgeInPredecessorsF′ : ℓ list∈ predecessors (set-to-list F′) ℓ′
      currentEdgeInPredecessorsF′ = predecessors-∈ (set-to-list F′) (ℓ , ℓ′) (set∈-to-list∈ (⊑-to-set∈ F′⊒F currentEdgeExistsInFlow))  
      case-nonemptyworklist : Dec (𝑓 ℓ x ⊑ lookup ℓ′ x) → Acc V._⊐_ x → Acc F._⊐_ F → Σ[ F̂ ∈ CFG ] Σ[ x ∈ FixedPoint F̂ ] ((y : FixedPoint F̂) → fp x V.⊑ fp y)
      case-nonemptyworklist (yes p) rs ts = mfp-extended x ι⊑x rs workList F ιF⊑F ts x⊑fp (λ ℓ′′ ℓ′′′ x₁ → ∈worklist-⇒-∈F ℓ′′ ℓ′′′ (there x₁)) ⋄x⊒fx' F⊒next x⊑⨆f F⊑⨆F
       where
        F′⊑F : F′ F.⊑ F
        F′⊑F = F.⊔-on-left-⊑ F.⊑-reflexive (F.⊑-trans (F.≡⇒⊑ (cong (next ℓ′) p)) (F⊒next ℓ′))
        F≡F′ : F ≡ F′
        F≡F′ = F.⊑-antisym F′⊒F F′⊑F
        ⋄x⊒fx' : (ℓ₁ ℓ′₁ : Label) → (ℓ₁ , ℓ′₁) set∈ F → ¬ (ℓ₁ , ℓ′₁) list∈ workList → lookup ℓ′₁ x ⊒ 𝓕 ℓ₁ (lookup ℓ₁ x)
        ⋄x⊒fx' l₃ l₄ x₁ x₂ with _×-≟_ FinP._≟_ FinP._≟_ (l₃ , l₄) (ℓ , ℓ′) 
        ⋄x⊒fx' _ _ x₁ x₂ | yes refl = p
        ⋄x⊒fx' l₃ l₄ x₁ x₂ | no ¬p = ⋄x⊒fx l₃ l₄ x₁ (λ x₃ → x₂ (⊎-elim-left (Inverse.from (∷↔ (λ x → (l₃ , l₄) ≡ x)) ⟨$⟩ x₃) ¬p ))
      case-nonemptyworklist (no ¬p) (acc rs) ts = mfp-extended x′ (V.⊑-trans ι⊑x x⊑x′) (rs x′ x⊏x′) (set-to-list (F′ Util.Subset.- F) 𝕃.++ outgoing (set-to-list F) ℓ′  𝕃.++ workList) F′ (F.⊑-trans ιF⊑F F′⊒F) (F-acc (F′ F.⊑? F) ts) x′⊑fp ∈worklist-⇒-∈F′ ⋄x′⊒fx′ F⊒next′ x′⊑⨆f F′⊑⨆F
       where
        F⊑F′ : F F.⊑ F′
        F⊑F′ = F.⊔-on-right-⊑ F.⊑-reflexive
        F-acc : Dec (F′ F.⊑ F) → Acc F._⊐_ F → Acc F._⊐_ F′
        F-acc (no ¬F′⊑F) (acc ts) = ts F′ (F.⊔-on-right-⊑ F.⊑-reflexive , (λ x₁ → ⊥-elim (¬F′⊑F (F.≡⇒⊑ (sym x₁)))))
        F-acc (yes F′⊑F) ts = acc-≡ (F.⊑-antisym F⊑F′ F′⊑F) ts
        x′ = x [ ℓ′ ]≔ v
        x⊑x′ : x V.⊑ x′
        x⊑x′ = ⊑-by-element L x ℓ′ (𝑓 ℓ x ⊔ lookup ℓ′ x) right-⊔-on-⊑
        x≠x′ : ¬ x ≡ x′
        x≠x′ x≡x′ = contradiction (
          begin
            𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
              ≡⟨ sym (lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x)) ⟩
              lookup ℓ′ x′
              ≡⟨ sym (cong (lookup ℓ′) x≡x′) ⟩
              lookup ℓ′ x
          ∎) ¬p
        
        x⊏x′ : x V.⊏ x′ 
        x⊏x′ = x⊑x′ , x≠x′
        x′⊑fp : (F̂ : CFG) → (F̂ F.⊒ F′) → (y : FixedPoint F̂) → x′ V.⊑ fp y
        x′⊑fp F̂ F̂⊒F′ y = ⊑-on-element' L x (fp y) ℓ′ v (x⊑fp F̂ (F.⊑-trans F′⊒F F̂⊒F′) y) (
          begin
            𝑓 ℓ x ⊔ lookup ℓ′ x
          ≡⟨⟩
            𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x 
          ⊑⟨ ⊔-on-⊑
             (begin
               𝓕 ℓ (lookup ℓ x)
             ⊑⟨ 𝓕-isMonotone ℓ (⊑-on-element L x (fp y) ℓ (x⊑fp F̂ (F.⊑-trans F′⊒F F̂⊒F′) y)) ⟩
               𝓕 ℓ (lookup ℓ (fp y))
             ∎)
             (begin
               lookup ℓ′ x
             ⊑⟨ ⊑-on-element L x (fp y) ℓ′ (x⊑fp F̂ (F.⊑-trans F′⊒F F̂⊒F′) y) ⟩
                lookup ℓ′ (fp y)
             ∎) ⟩ 
             𝓕 ℓ (lookup ℓ (fp y)) ⊔ lookup ℓ′ (fp y)
          ⊑⟨ right-⊔-on-⊑ ⟩
             lookup ℓ′ initial ⊔ 𝓕 ℓ (lookup ℓ (fp y)) ⊔ lookup ℓ′ (fp y)
          ≡⟨ sym (⊔-assoc _ _ _) ⟩
             (lookup ℓ′ initial ⊔ 𝓕 ℓ (lookup ℓ (fp y))) ⊔ lookup ℓ′ (fp y)
          {-  We weten ook dat (ℓ , ℓ′) ∈ F, want alles in de worklist komt uit F, dus dan moet hij ook in F̂ zitten. -}
          ≡⟨  fixed⇒reductive F̂ (fp y) (isFixedPoint y) ℓ ℓ′ (⊑-to-set∈ {(ℓ , ℓ′)} {F} {F̂} (F.⊑-trans F′⊒F F̂⊒F′) (∈worklist-⇒-∈F ℓ ℓ′ (here refl)))  ⟩ 
             lookup ℓ′ (fp y)
          ∎)
        
        ∈worklist-⇒-∈F′ : (ℓ′′ ℓ′′′ : Label) → (ℓ′′ , ℓ′′′) list∈ set-to-list (F′ Util.Subset.- F) 𝕃.++ outgoing (set-to-list F) ℓ′  𝕃.++ workList → (ℓ′′ , ℓ′′′) set∈ F′
        ∈worklist-⇒-∈F′ ℓ′′ ℓ′′′ e∈wl =
            let r = Inverse.from (Data.List.Any.Properties.++↔ {P = λ x₁ → (ℓ′′ , ℓ′′′) ≡ x₁} {xs = set-to-list (F′ Util.Subset.- F)} {ys = outgoing (set-to-list F) ℓ′ 𝕃.++ workList}) ⟨$⟩ e∈wl
            in case r of λ where
                (inj₁ x₁) → proj₁ (Equivalence.to ⊓⇔× ⟨$⟩ list∈-to-set∈ x₁)
                (inj₂ y₁) → let t = Inverse.from (Data.List.Any.Properties.++↔ {P = λ x₁ → (ℓ′′ , ℓ′′′) ≡ x₁} {xs = outgoing (set-to-list F) ℓ′} {ys = workList}) ⟨$⟩ y₁
                            in case t of λ where
                                (inj₁ x₂) → ⊑-to-set∈ F′⊒F (list∈-to-set∈ (outgoing-⊆ (set-to-list F) ℓ′ x₂)) 
                                (inj₂ y) → ⊑-to-set∈ {ℓ′′ , ℓ′′′} {F} {F′} F′⊒F (∈worklist-⇒-∈F ℓ′′ ℓ′′′ (there y)) 
        
        lemma-l₄≠ℓ′ : ∀{l₃ l₄} → ¬( l₃ ≡ ℓ′ ) → ¬( l₄ ≡ ℓ′ ) → 𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) ≡ 𝓕 l₃ (lookup l₃ x) ⊔ lookup l₄ x
        lemma-l₄≠ℓ′ {l₃} {l₄} l₃≠ℓ′ l₄≠ℓ′ =
          begin
          𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 l₃ i ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) (lookup∘update′ l₃≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 l₃ (lookup l₃ x) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 l₃ (lookup l₃ x) ⊔ i) (lookup∘update′ l₄≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 l₃ (lookup l₃ x) ⊔ lookup l₄ x
          ∎
        
        lemma-l₄≡ℓ′ : ∀{l₃ l₄} → ¬( l₃ ≡ ℓ′ ) → l₄ ≡ ℓ′ → 𝓕 l₃ (lookup l₃ x) ⊑ lookup ℓ′ x
                   → 𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup l₄ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) ≡ 𝓕 ℓ (lookup ℓ x) ⊔ lookup l₄ x
        lemma-l₄≡ℓ′ {l₃} {.ℓ′} l₃≠ℓ′ refl y =
          begin
          𝓕 l₃ (lookup l₃ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 l₃ i ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) (lookup∘update′ l₃≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 l₃ (lookup l₃ x) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 l₃ (lookup l₃ x) ⊔ i) (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 l₃ (lookup l₃ x) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ sym (⊔-assoc _ _ _) ⟨ trans ⟩ cong (_⊔ lookup ℓ′ x) (⊔-comm (𝓕 l₃ (lookup l₃ x)) (𝓕 ℓ (lookup ℓ x))) ⟨ trans ⟩ ⊔-assoc _ _ _ ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 l₃ (lookup l₃ x) ⊔ lookup ℓ′ x
          ≡⟨ cong (_⊔_ (𝓕 ℓ (lookup ℓ x))) y  ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ∎
        
        lemma-ℓ≠ℓ′ : ¬( ℓ ≡ ℓ′ ) → 𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) ≡ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
        lemma-ℓ≠ℓ′ ℓ≠ℓ′ =
          begin
          𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ lookup ℓ′ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)
          ≡⟨ cong (\i → 𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ i) (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 ℓ (lookup ℓ (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ cong (\i → 𝓕 ℓ i ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x) (lookup∘update′ ℓ≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)) ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ≡⟨ sym (⊔-assoc _ _ _) ⟩
          (𝓕 ℓ (lookup ℓ x) ⊔ 𝓕 ℓ (lookup ℓ x)) ⊔ lookup ℓ′ x
          ≡⟨ cong (\i → i ⊔ lookup ℓ′ x) (⊔-idem (𝓕 ℓ (lookup ℓ x))) ⟩
          𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x
          ∎
        
        ⋄x′⊒fx′ : (ℓ₁ ℓ′₁ : Label) → (ℓ₁ , ℓ′₁) set∈ F′ → ¬ (ℓ₁ , ℓ′₁) list∈ set-to-list (F′ Util.Subset.- F) 𝕃.++ outgoing (set-to-list F) ℓ′ 𝕃.++ workList → lookup ℓ′₁ x′ ⊒ 𝓕 ℓ₁ (lookup ℓ₁ x′)
        ⋄x′⊒fx′ l₃ l₄ l₃,l₄set∈F′ l₃,l₄∉workList with (l₃ , l₄) set∈? F | _×-≟_ FinP._≟_ FinP._≟_ (l₃ , l₄) (ℓ , ℓ′)
        ⋄x′⊒fx′ _ _ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | yes refl with ℓ FinP.≟ ℓ′
        ⋄x′⊒fx′ _ _ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | yes refl | (yes refl) = contradiction (++ʳ (set-to-list (F′ Util.Subset.- F)) (++ˡ (outgoing-∈ (set-to-list F) (ℓ , ℓ′) (set∈-to-list∈ l₃,l₄set∈F)))) l₃,l₄∉workList
        ⋄x′⊒fx′ _ _ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | yes refl | (no ¬p) = trans (lemma-ℓ≠ℓ′ ¬p) (sym (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)))
        ⋄x′⊒fx′ l₃ l₄ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | no ¬p with l₃ FinP.≟ ℓ′ | l₄ FinP.≟ ℓ′ | ⋄x⊒fx l₃ l₄ (¬∁ (λ x₃ → l₃,l₄∉workList (++ˡ (set∈-to-list∈ (set∈-- l₃,l₄set∈F′ (set∈∁⇒set∉ x₃)))))) (λ x₁ → l₃,l₄∉workList (++ʳ (set-to-list (F′ Util.Subset.- F)) (++ʳ (outgoing (set-to-list F) ℓ′) (⊎-elim-left (Inverse.from (∷↔ (λ x → (l₃ , l₄) ≡ x)) ⟨$⟩ x₁) ¬p))))
        ⋄x′⊒fx′ _ l₄ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | no ¬p | yes refl | _ | _ = contradiction (++ʳ (set-to-list (F′ Util.Subset.- F)) (++ˡ (outgoing-∈ (set-to-list F) (ℓ′ , l₄) (set∈-to-list∈ l₃,l₄set∈F)))) l₃,l₄∉workList
        ⋄x′⊒fx′ l₃ _ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | no ¬p | no l₃≠ℓ′ | yes refl | y = trans (lemma-l₄≡ℓ′ l₃≠ℓ′ refl y) (sym (lookup∘update ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))) 
        ⋄x′⊒fx′ l₃ l₄ l₃,l₄set∈F′ l₃,l₄∉workList | yes l₃,l₄set∈F | no ¬p | no l₃≠ℓ′ | no l₄≠ℓ′ | y = trans (lemma-l₄≠ℓ′ l₃≠ℓ′ l₄≠ℓ′) (trans y (sym (lookup∘update′ l₄≠ℓ′ x (𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x)))) 
        ⋄x′⊒fx′ l₃ l₄ l₃,l₄set∈F′ l₃,l₄∉workList | no l₃,l₄set∉F | _ = contradiction (++ˡ (set∈-to-list∈ (set∈-- l₃,l₄set∈F′ l₃,l₄set∉F))) l₃,l₄∉workList

        fx⊑fx′-pointwise : (z : Label) → 𝑓 z x ⊑ 𝑓 z x′
        fx⊑fx′-pointwise z with z FinP.≟ ℓ′
        fx⊑fx′-pointwise z | yes refl =
          begin
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
        fx⊑fx′-pointwise z | no z≠ℓ′ =
          begin
          𝓕 z (lookup z x) ⊔ 𝓕 z (lookup z (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
          ≡⟨ cong (\i → 𝓕 z (lookup z x) ⊔ 𝓕 z i) (lookup∘update′ z≠ℓ′ _ _) ⟩ 
          𝓕 z (lookup z x) ⊔ 𝓕 z (lookup z x)
          ≡⟨ ⊔-idem _ ⟩ 
          𝓕 z (lookup z x)
          ≡⟨ cong (𝓕 z) (sym (lookup∘update′ z≠ℓ′ _ _)) ⟩ 
          𝓕 z (lookup z (x [ ℓ′ ]≔ 𝓕 ℓ (lookup ℓ x) ⊔ lookup ℓ′ x))
          ∎
        
        ⨆fx⊑⨆fx′ : (ℓ′′ : Label) →  ⨆ (𝕃.map (flip 𝑓 x) (predecessors (set-to-list F) ℓ′′)) ⊑ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′′))
        ⨆fx⊑⨆fx′ ℓ′′ =
          begin
          ⨆ (𝕃.map (flip 𝑓 x) (predecessors (set-to-list F) ℓ′′))
          ⊑⟨ ⨆⊑⨆-pointwise _ _ (Pointwise.rec (λ {v} {v₁} v₂ → Pointwise.Rel _⊑_ (𝕃.map (flip 𝑓 x) v) (𝕃.map (flip 𝑓 x′) v₁)) (λ {a} {b} {xs} {ys} {xs∼ys} x∼y x₂ → f {a} {b} {xs} {ys} {xs∼ys} x∼y x₂) Pointwise.[] (Pointwise.≡⇒Rel≡ (refl {_} {_} {predecessors (set-to-list F) ℓ′′}))) ⟩
          ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F) ℓ′′))
          ⊑⟨ ⨆-mono (map-mono _ (predecessors-mono _ (set-to-list-mono (⊑-to-set∈ F′⊒F))))  ⟩
          ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′′))
          ∎
         where f : {a : Label} {b : Label} {xs ys : List Label} {xs∼ys : Pointwise.Rel _≡_ xs ys} (x∼y : a ≡ b) → Pointwise.Rel _⊑_ (𝕃.map (flip 𝑓 x) xs) (𝕃.map (flip 𝑓 x′) ys) → Pointwise.Rel _⊑_ (flip 𝑓 x a ∷ 𝕃.map (flip 𝑓 x) xs) (flip 𝑓 x′ b ∷ 𝕃.map (flip 𝑓 x′) ys)
               f {a} {.a} refl x₁ = fx⊑fx′-pointwise a Pointwise.∷ x₁  
        
        x′⊑⨆f : (ℓ′′ : Label) → lookup ℓ′′ x′ ⊑ lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′′ ))
        x′⊑⨆f ℓ′′ with ℓ′′ FinP.≟ ℓ′
        x′⊑⨆f .ℓ′ | yes refl =
          begin
          lookup ℓ′ x′
          ≡⟨ lookup∘update ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x) ⟩
          𝑓 ℓ x ⊔ lookup ℓ′ x
          ⊑⟨ ⊔-on-left-⊑
            (begin
            𝑓 ℓ x
            ⊑⟨ fx⊑fx′-pointwise _ ⟩
            𝑓 ℓ x′
            ⊑⟨ x⊑⨆x (𝑓 ℓ x′) (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′)) (Inverse.to map-∈↔ ⟨$⟩ (ℓ , (currentEdgeInPredecessorsF′ , refl)) ) ⟩   
            ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′))
            ⊑⟨ right-⊔-on-⊑ ⟩
            lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′))
            ∎)
            (begin
            lookup ℓ′ x                             
            ⊑⟨ x⊑⨆f ℓ′  ⟩
            lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors (set-to-list F) ℓ′))
            ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′ initial)) ⊔-monotone-left (⨆fx⊑⨆fx′ ℓ′) ⟩ 
            lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′))
            ∎) ⟩
          lookup ℓ′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′))
          ∎ 
        x′⊑⨆f ℓ′′ | no ℓ′′≠ℓ′ =
          begin
          lookup ℓ′′ x′
          ≡⟨ lookup∘update′ ℓ′′≠ℓ′ x (𝑓 ℓ x ⊔ lookup ℓ′ x) ⟩
          lookup ℓ′′ x
          ⊑⟨ x⊑⨆f ℓ′′ ⟩
          lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x) (predecessors (set-to-list F) ℓ′′))
          ⊑⟨ ⊑-cong (_⊔_ (lookup ℓ′′ initial)) ⊔-monotone-left (⨆fx⊑⨆fx′ ℓ′′) ⟩
          lookup ℓ′′ initial ⊔ ⨆ (𝕃.map (flip 𝑓 x′) (predecessors (set-to-list F′) ℓ′′))
          ∎

        F⊒next′ : (ℓ′′ : Label) → F′ F.⊒ next ℓ′′ (lookup ℓ′′ x′)
        F⊒next′ ℓ′′ with ℓ′′ FinP.≟ ℓ′
        F⊒next′ _ | yes refl = F.⊔-on-right-⊑′ (F.≡⇒⊑ (cong (next ℓ′) (lookup∘update ℓ′ x _)))
        F⊒next′ ℓ′′ | no ¬p = F.⊔-on-right-⊑ (F.⊑-trans (F.≡⇒⊑ (cong (next ℓ′′) (lookup∘update′ ¬p _ _))) (F⊒next ℓ′′))

        F′⊑⨆F : F′ F.⊑ initial-F F.⊔ F.⨆ (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) (toList (allFin n)))
        F′⊑⨆F = F.⊔-on-left-⊑ (F.⊑-trans F⊑⨆F (F.⊔-on-⊑ F.⊑-reflexive (F.⨆⊑⨆-pointwise (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) (toList (allFin n))) (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) (toList (allFin n))) (Pointwise.rec
                  (λ {v₁} {v₂} x₁ → Pointwise.Rel F._⊑_ (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) v₁) (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) v₂))
                  (λ {a} {b} {xs} {ys} {xs∼ys} x∼y x₂ → f {a} {b} {xs} {ys} {xs∼ys} x∼y x₂)
                  Pointwise.[]
                  (Pointwise.≡⇒Rel≡ refl))))) (F.⊔-on-right-⊑′ (F.⊑⨆x (next ℓ′ v) (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) (toList (allFin n))) (Inverse.to Any↔ ⟨$⟩ ((next ℓ′ (lookup ℓ′ x′)) , (Inverse.to map-∈↔ ⟨$⟩ (ℓ′ , ((∈⇒List-∈ (∈-allFin ℓ′)) , refl)) , F.≡⇒⊑ (sym (cong (next ℓ′) (lookup∘update ℓ′ _ _))))))))
         where 
          f : {x₁ : Fin n} {y : Fin n} {xs ys : List (Fin n)} {xs∼ys : Pointwise.Rel _≡_ xs ys} (x∼y : x₁ ≡ y) → Pointwise.Rel F._⊑_ (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) xs) (𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) ys) → Pointwise.Rel F._⊑_ (next x₁ (lookup x₁ x) ∷ 𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x)) xs) (next y (lookup y x′) ∷ 𝕃.map (λ ℓ′′ → next ℓ′′ (lookup ℓ′′ x′)) ys)
          f {a} {.a} refl x₁ = next-isMonotone a (⊑-on-element L x x′ a x⊑x′) Pointwise.∷ x₁
               
    mfp : Σ[ F̂ ∈ CFG ] Σ[ x ∈ FixedPoint F̂ ] ((y : FixedPoint F̂) → fp x V.⊑ fp y)
    mfp =
      mfp-extended
        initial
        (V.⊔-idem initial)
        (V.⊐-isWellFounded initial)
        (set-to-list initial-F)
        initial-F
        F.⊑-reflexive
        (F.⊐-isWellFounded initial-F)
        (λ F̂ x y → initial⊑fp F̂ y)
        (λ ℓ′′ ℓ′′′ → list∈-to-set∈)
        (λ ℓ ℓ′ x x₁ → contradiction (set∈-to-list∈ x) x₁)
        (λ ℓ → F.x⊑⨆x (next ℓ (lookup ℓ initial)) (𝕃.map (λ ℓ → next ℓ (lookup ℓ initial)) (Data.Vec.toList (allFin n))) (Inverse.to map-∈↔ ⟨$⟩ (ℓ , ((∈⇒List-∈ (∈-allFin ℓ)) , refl))))
        (λ ℓ′ → ⊔-on-right-⊑ ⊑-reflexive)
        (F.⊔-on-right-⊑ F.⊑-reflexive)
        
    mfp○ : V.ℂ
    mfp○ = fp (proj₁ (proj₂ mfp)) 
  
    mfp● : V.ℂ
    mfp● = tabulate 𝓕 ⊛ mfp○ 

    mfp-result : V.ℂ × V.ℂ
    mfp-result = (mfp○ , mfp●)

