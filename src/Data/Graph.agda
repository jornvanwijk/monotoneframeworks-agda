open import Data.Nat as ℕ hiding (_≟_)
open import Data.Product
open import Data.List as 𝕃
open import Data.Fin
open import Data.Fin.Properties
open import Function
import Data.Vec as 𝕍
open 𝕍 hiding (_∈_) 
open import Relation.Nullary.Decidable
open import Monotonicity
open import Util.Subset
open import Data.List.Any
open import Data.List.Any.Properties  hiding (swap)
open import Data.Unit renaming (_≟_ to _≟⊤_)
import Data.List.Any.Membership as Any-Properties
open Any-Properties
open import Relation.Binary.PropositionalEquality
open Membership-≡ renaming (_∈_ to _list∈_ ; _⊆_ to _list⊆_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Bool renaming (_≟_ to _≟𝔹_)
open import Function.Inverse using (Inverse)
open import Function.Equality using (_⟨$⟩_)
open import Data.List.All
open import Relation.Unary using (Decidable)
open import Util.Product
open import Data.Bool.Properties
open import Function.Equivalence using (Equivalence)
open import Util.List.All.Properties
open import Util.List.Any.Properties

module Data.Graph (n : ℕ) where
  Edge : Set
  Edge = Fin n × Fin n

  Graph : Set
  Graph = List Edge

  _ᴿ : Graph -> Graph
  _ᴿ = 𝕃.map swap

 
  outgoing : Graph → Fin n → List Edge
  outgoing x ℓ = filter (⌊_⌋ ∘ (_≟ ℓ) ∘ proj₁) x

  successors : Graph → Fin n → List (Fin n)
  successors x ℓ = 𝕃.map proj₂ (outgoing x ℓ)

  incoming : Graph → Fin n → List Edge
  incoming x ℓ′ = filter (⌊_⌋ ∘ (_≟ ℓ′) ∘ proj₂) x

  predecessors : Graph → Fin n → List (Fin n)
  predecessors x ℓ′ = 𝕃.map proj₁ (incoming x ℓ′)


  module Properties (F : Graph) where



    incoming-⊆ : (ℓ′ : Fin n) → incoming F ℓ′ list⊆ F
    incoming-⊆ ℓ′ = filter-⊆ (⌊_⌋ ∘ (_≟ ℓ′) ∘ proj₂) F

    incoming-∈ : (e : Edge) → e list∈ F → e list∈ incoming F (proj₂ e)
    incoming-∈ (ℓ , ℓ′) x =  filter-∈ (⌊_⌋ ∘ (_≟ ℓ′) ∘ proj₂) F x obs
      where obs : ⌊ proj₂ (ℓ , ℓ′) ≟ ℓ′ ⌋ ≡ true  
            obs with proj₂ (ℓ , ℓ′) ≟ ℓ′
            obs | yes q = refl   -- this could probably be a lot nicer.
            obs | no ¬q = contradiction refl ¬q


    
    incoming-mono : (ℓ : Fin n) → Monotone _list⊆_ (flip incoming ℓ)
    incoming-mono ℓ′ x₁ x₃ = filter-mono (⌊_⌋ ∘ (_≟ ℓ′) ∘ proj₂) (⌊_⌋ ∘ (_≟ ℓ′) ∘ proj₂) (λ x x₂ → x₂) _ _ x₁ x₃



    outgoing-⊆ : (ℓ : Fin n) → outgoing F ℓ list⊆ F
    outgoing-⊆ ℓ = filter-⊆ (⌊_⌋ ∘ (_≟ ℓ) ∘ proj₁) F

    outgoing-mono : (ℓ : Fin n) → Monotone _list⊆_ (flip outgoing ℓ)
    outgoing-mono ℓ {x} {y} x₁ {x₂} x₃ = filter-mono (⌊_⌋ ∘ (_≟ ℓ) ∘ proj₁) (⌊_⌋ ∘ (_≟ ℓ) ∘ proj₁) (λ x₄ x₅ → x₅) x y x₁ x₃





    outgoing-∈ : (e : Edge) → e list∈ F → e list∈ outgoing F (proj₁ e)
    outgoing-∈ (ℓ , ℓ′) x = filter-∈ (⌊_⌋ ∘ (_≟ ℓ) ∘ proj₁) F x obs
      where obs : ⌊ proj₁ (ℓ , ℓ′) ≟ ℓ ⌋ ≡ true  
            obs with proj₁ (ℓ , ℓ′) ≟ ℓ
            obs | yes q = refl   -- this could probably be a lot nicer.
            obs | no ¬q = contradiction refl ¬q

    predecessors-⊆ : (ℓ : Fin n) → predecessors F ℓ list⊆ 𝕃.map proj₁ F
    predecessors-⊆ ℓ {ℓ′} x = let (a , b , c) = Inverse.from map-∈↔ ⟨$⟩ x
                              in Inverse.to Any↔ ⟨$⟩ ((proj₁ a) , ((Inverse.to map-∈↔ ⟨$⟩ (_ , (incoming-⊆ ℓ b , refl))) , c))

    predecessors-⊆′ : (ℓ′ : Fin n) → Σ[ ℓ ∈ Fin n ] ℓ list∈ predecessors F ℓ′ → Σ[ ℓ ∈ Fin n ] (ℓ , ℓ′) list∈ F
    predecessors-⊆′ ℓ′ (ℓ , ℓ∈pred) = ℓ , (let (a , b , c) = Inverse.from map-∈↔ ⟨$⟩ ℓ∈pred
                                               (d , e) = filter-∈? ((_≟ ℓ′) ∘ proj₂) F b
                                          in Inverse.to Any↔ ⟨$⟩ (a , ((incoming-⊆ ℓ′ b) , (≡×⇒≡ (c , (sym e)))))) 

    predecessors-∈ : (e : Edge) → e list∈ F → proj₁ e list∈ predecessors F (proj₂ e)
    predecessors-∈ e x = Inverse.to map-∈↔ ⟨$⟩ (e , ((incoming-∈ e x) , refl))

  open Properties public



  predecessors-mono : (ℓ : Fin n) → Monotone₂ _list⊆_ _list⊆_ (flip predecessors ℓ) 
  predecessors-mono ℓ {x} {y} x₁ x₃ = map-mono _ (incoming-mono x ℓ x₁) x₃
