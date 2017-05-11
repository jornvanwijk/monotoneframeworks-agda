import Level
open import Data.Nat hiding (_⊔_ ; _⊓_ ; _≟_)
module LatticeTheory.TotalFunctionSpace where
open import LatticeTheory.Core
open import LatticeTheory.Product
open import LatticeTheory.Vector
open import Data.Fin
open import Data.Fin.Dec
open import Data.Fin.Properties hiding (_≟_)
open import Data.Product
open import Data.Product renaming (_×_ to _⋀_)
open import Data.Vec
open import Function.Equality using (_⟨$⟩_)
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Vec.Equality
open import Function
open import Util.Vector
open import Function.Inverse hiding (sym ; _∘_)
open import LatticeTheory.ByBijection
open import Data.Vec.Properties


postulate
  fun-ext : ∀{a b} → Extensionality a b
module _ {a} {b} (A : Set a) (inv : Σ[ n ∈ ℕ ] (A ↔ Fin n)) (L : BoundedSemiLattice b) where    
  private
    n : ℕ
    n = proj₁ inv
    module V where
      open BoundedSemiLattice (Vecᴸ L n) public
    module L where
      open BoundedSemiLattice L public
    module F where
    open Inverse (proj₂ inv)

    mkVec : (A → L.ℂ) → Vec L.ℂ n
    mkVec f = Data.Vec.map (λ x → f (from ⟨$⟩ x)) (allFin n)
  
    mkFun : Vec L.ℂ n → A → L.ℂ
    mkFun v x = lookup (to ⟨$⟩ x) v
  
    open ≡-Reasoning
    right-inverse' : (x : Vec L.ℂ n) → mkVec (mkFun x) ≡ x
    right-inverse' x = begin
         mkVec (mkFun x)
         ≡⟨⟩
         Data.Vec.map (λ x₁ → lookup (to ⟨$⟩ (from ⟨$⟩ x₁)) x) (tabulate (λ x₁ → x₁))
         ≡⟨ sym (tabulate-∘ (λ x₁ → lookup (to ⟨$⟩ (from ⟨$⟩ x₁)) x) Function.id)  ⟩
         tabulate (λ x₁ → lookup (to ⟨$⟩ (from ⟨$⟩ x₁)) x)
         ≡⟨ tabulate-allFin (λ x₁ → lookup (to ⟨$⟩ (from ⟨$⟩ x₁)) x) ⟩
         Data.Vec.map (λ x₁ → lookup (to ⟨$⟩ (from ⟨$⟩ x₁)) x) (allFin n)
         ≡⟨ map-cong (λ x₁ → cong (flip lookup x) (right-inverse-of x₁)) (allFin n) ⟩
         Data.Vec.map (λ x₁ → lookup  x₁ x) (allFin n)
         ≡⟨ map-lookup-allFin x ⟩
         x ∎
    left-inverse' : (f : A → L.ℂ) → mkFun (mkVec f) ≡ f
    left-inverse' f = fun-ext (λ x → begin
                         mkFun (mkVec f) x
                         ≡⟨⟩
                         lookup (to ⟨$⟩ x) (Data.Vec.map (λ x → f (from ⟨$⟩ x)) (allFin n))
                         ≡⟨ lookup-map (to ⟨$⟩ x) (λ x → f (from ⟨$⟩ x)) (allFin n) ⟩
                         f (from ⟨$⟩ (lookup (to ⟨$⟩ x) (allFin n)))
                         ≡⟨ cong (f $_) (subst (λ y → from ⟨$⟩ y ≡ x) (sym (lookup∘tabulate Function.id (to ⟨$⟩ x))) (left-inverse-of x)) ⟩
                         f x
                         ∎)
  TFS↔Vecᴸ : (A → L.ℂ) ↔ Vec L.ℂ n
  TFS↔Vecᴸ = record
            { to = →-to-⟶ mkVec
            ; from = →-to-⟶ mkFun
            ; inverse-of = record
              { left-inverse-of = left-inverse'
              ; right-inverse-of = right-inverse'
              }
            }

  infixr 2 _-[_]→_
  _-[_]→_ : BoundedSemiLattice (b Level.⊔ a) --Vecᴸ ? ?
  _-[_]→_ = fromBijectionᴸ {b Level.⊔ a} {b} (A → L.ℂ) (Vecᴸ L n) TFS↔Vecᴸ 

  open BoundedSemiLattice (_-[_]→_)
  open LatticeTheory.ByBijection.Properties
  open import Util.Vector
  
  $-⊔ : (f g : A → L.ℂ) → (x : A) → (f ⊔ g) x ≡ f x L.⊔ g x
  $-⊔ f g x = begin
              (f ⊔ g) x
              ≡⟨ sym (lookup-⊔ L (Inverse.to (proj₂ inv) ⟨$⟩ x) _ _) ⟩
              lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) (Data.Vec.map (λ x₁ → f (Inverse.from (proj₂ inv) ⟨$⟩ x₁)) (tabulate Function.id))
              L.⊔
              lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) (Data.Vec.map (λ x₁ → g (Inverse.from (proj₂ inv) ⟨$⟩ x₁)) (tabulate Function.id))
              ≡⟨ L.⊔-cong₂ (lemma f) (lemma g) ⟩ 
              f x L.⊔ g x
              ∎ 
          where lemma : (h : A → L.ℂ) → lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) (Data.Vec.map (λ x₁ → h (Inverse.from (proj₂ inv) ⟨$⟩ x₁)) (tabulate Function.id)) ≡ h x
                lemma h = begin
                  lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) (Data.Vec.map (λ x₁ → h (Inverse.from (proj₂ inv) ⟨$⟩ x₁)) (tabulate Function.id))
                  ≡⟨ cong (λ z → lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) z) (sym (tabulate-∘ _ _)) ⟩
                  lookup (Inverse.to (proj₂ inv) ⟨$⟩ x) (tabulate (λ x₁ → h (Inverse.from (proj₂ inv) ⟨$⟩ x₁)))
                  ≡⟨ lookup∘tabulate (λ x₁ → h (Inverse.from (proj₂ inv) ⟨$⟩ x₁)) (Inverse.to (proj₂ inv) ⟨$⟩ x) ⟩
                  h (Inverse.from (proj₂ inv) ⟨$⟩ (Inverse.to (proj₂ inv) ⟨$⟩ x))
                  ≡⟨ cong h (Inverse.left-inverse-of (proj₂ inv) x) ⟩
                  h x
                  ∎

  $-⊑' : (f g : A → L.ℂ) → ((x : A) → f x L.⊑ g x) → f ⊑ g
  $-⊑' f g x = begin
               f ⊔ g
               ≡⟨ fun-ext (λ y → begin
                                 (f ⊔ g) y
                                 ≡⟨ $-⊔ (λ v → f v) (λ v → g v) y ⟩
                                 f y L.⊔ g y
                                 ≡⟨ x y ⟩
                                 g y
                                 ∎) ⟩
               g
               ∎
  $-⊑ : (f g : A → L.ℂ) → (x : A) → f ⊑ g → f x L.⊑ g x
  $-⊑ f g x x₁ = begin
                  f x L.⊔ g x
                  ≡⟨ sym ($-⊔ f g x) ⟩
                  (f ⊔ g) x 
                  ≡⟨ cong (_$ x) x₁ ⟩ 
                  g x
                  ∎
