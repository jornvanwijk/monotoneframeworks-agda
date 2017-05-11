open import Algebra
open import Algebra.Structures
open import Data.Bool
open import Data.Bool.Properties
open import Data.Empty
open import Data.Fin hiding (_-_)
open import Data.Fin.Dec
open import Data.Fin.Subset renaming (_∈_ to _setFin∈_ ; _∉_ to _setFin∉_ ; _⊆_ to _setFin⊆_; ⊥ to ∅)
open import Data.Fin.Subset.Properties
open import Data.List
open import Data.List.Any
open import Data.List.Any.Membership as AnyMembership 
open import Data.List.Any.Properties
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Vec hiding (toList ; _∈_)
open import Data.Vec.Properties
open import Function
open import Function.Equality hiding (cong ; _∘_)
open import Function.Equivalence hiding (sym ; _∘_)
open import Function.Inverse hiding (sym ; _∘_)
open import Monotonicity
open import Relation.Binary.PropositionalEquality    
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Util.List.All.Properties
open import Util.List.Any.Properties
open import Util.Vector
open Membership-≡ renaming (_∈_ to _list∈_ ; _⊆_ to _list⊆_)
open ≡-Reasoning
module Util.Subset where

                                                                             
  _-_ : ∀{n} → Subset n → Subset n → Subset n
  x - y = x ∩ (∁ y)  -- x `zipWith _∧_` (map ¬_ y)

  -- todo remove double negation
  setFin∈∁⇒setFin∉ : ∀{n} → {a : Subset n} → {x : Fin n} → x setFin∈ ∁ a → ¬ x setFin∈ a
  setFin∈∁⇒setFin∉ {n} {a} {x} x₁ x₂ = contradiction (Inverse.to []=↔lookup ⟨$⟩ x₂) (not-¬ (Equivalence.to T-not-≡ ⟨$⟩ (Equivalence.from T-≡ ⟨$⟩ (
           begin
           not (lookup x a)
           ≡⟨ sym (cong (_$ lookup x a) (lookup-replicate x not)) ⟩
           lookup x (Data.Vec.replicate not) (lookup x a)
           ≡⟨ sym (lookup-⊛ x (Data.Vec.replicate not) a) ⟩
           lookup x (∁ a)
           ≡⟨ Inverse.to []=↔lookup ⟨$⟩ x₁ ⟩
           true
           ∎))))
    

  -- todo rewrite in terms of setFin∈∁⇒setFin∉
  setFin¬∁ : ∀{n} → {a : Subset n} → {x : Fin n} → ¬ x setFin∈ ∁ a → x setFin∈ a
  setFin¬∁ {n} {a} {x} x₁ = Inverse.from []=↔lookup ⟨$⟩ ¬-not (λ i → x₁ (Inverse.from []=↔lookup ⟨$⟩ (
     begin
     lookup x (Data.Vec.replicate not ⊛ a)
     ≡⟨ lookup-⊛ x (Data.Vec.replicate not) a ⟩
     (lookup x (Data.Vec.replicate not) $ lookup x a)
     ≡⟨ cong (_$ lookup x a) (lookup-replicate x not)  ⟩
     not (lookup x a)
     ≡⟨ cong not i ⟩
     true
     ∎)))
  setFin∈-- : ∀{n} → { a b : Subset n} → {x : Fin n} → x setFin∈ a → x setFin∉ b → x setFin∈ a - b
  setFin∈-- {.(suc _)} {.(true ∷ _)} {outside ∷ b} here x₂ = here
  setFin∈-- {.(suc _)} {.(true ∷ _)} {true ∷ b} here x₂ = ⊥-elim (x₂ here)
  setFin∈-- {.(suc _)} {.(_ ∷ _)} {x ∷ b} (there x₁) x₂ = there (setFin∈-- x₁ (λ x₃ → ⊥-elim (x₂ (there x₃))))

  ⊔⇔⊎-fin : ∀{n} → {x : Fin n} → {a b : Subset n} → x setFin∈ (a ∪ b) ⇔ (x setFin∈ a ⊎ x setFin∈ b)
  ⊔⇔⊎-fin = ∪⇔⊎
  
  ⊓⇔×-fin : ∀ {n} {p₁ p₂ : Subset n} {x} → x setFin∈ p₁ ∩ p₂ ⇔ (x setFin∈ p₁ × x setFin∈ p₂)
  ⊓⇔×-fin = equivalence (to _ _) from
   where
     to : ∀ {n} (p₁ p₂ : Subset n) {x} → x setFin∈ p₁ ∩ p₂ → x setFin∈ p₁ × x setFin∈ p₂
     to [] [] ()
     to (true ∷ p₁) (.true ∷ p₂) here = here , here
     to (_ ∷ p₁) (_ ∷ p₂) (there x₃) = Data.Product.map there there (to p₁ p₂ x₃) 
     
     from : ∀ {n} {p₁ p₂ : Subset n} {x} → x setFin∈ p₁ × x setFin∈ p₂ → x setFin∈ p₁ ∩ p₂
     from (here , here) = here
     from (there proj₃ , there proj₄) = there (from (proj₃ , proj₄))


  setFin∈--' : ∀{n} → { a b : Subset n} → {x : Fin n} → x setFin∉ b → x setFin∈ a - b → x setFin∈ a
  setFin∈--' x₁ x₂ = proj₁ (Equivalence.to ⊓⇔×-fin ⟨$⟩ x₂) 
  
  setFin∈-cong₂ : ∀{n} → {a b : Fin n} → {c d : Subset n} → a ≡ b → c ≡ d → a setFin∈ c → b setFin∈ d
  setFin∈-cong₂ refl refl x₂ = x₂

  setFin∉-right : ∀{n} → {A B : Subset n} {x : Fin n} → x setFin∈ A ∪ B → x setFin∉ B → x setFin∈ A
  setFin∉-right {.0} {[]} {[]} () x₂
  setFin∉-right {.(suc _)} {outside ∷ A} {.true ∷ B} here x₄ = ⊥-elim (x₄ here)
  setFin∉-right {.(suc _)} {outside ∷ A} {x₁ ∷ B} (there x₃) x₄ = there (setFin∉-right x₃ (λ x → ⊥-elim (x₄ (there x))))
  setFin∉-right {.(suc _)} {true ∷ A} {x₁ ∷ B} here x₄ = here
  setFin∉-right {.(suc _)} {true ∷ A} {x₁ ∷ B} (there x₃) x₄ = there (setFin∉-right x₃ (λ x → ⊥-elim (x₄ (there x))))

  setFin∉-left : ∀{n} → {A B : Subset n} {x : Fin n} → x setFin∈ A ∪ B → x setFin∉ A → x setFin∈ B
  setFin∉-left {n} {A} {B} {x} x∈A∪B x∉A = setFin∉-right
                                       (setFin∈-cong₂ refl
                                        (IsLattice.∨-comm
                                         (IsDistributiveLattice.isLattice
                                          (IsBooleanAlgebra.isDistributiveLattice
                                           (BooleanAlgebra.isBooleanAlgebra
                                            (Data.Fin.Subset.booleanAlgebra _))))
                                         A B)
                                        x∈A∪B)
                                       x∉A

  toFinList : ∀{n} → Subset n → List (Fin n)
  toFinList {n} x = Data.List.filter (λ y → ⌊ y ∈? x ⌋) (Data.Vec.toList (allFin n))

  finList-to-set : ∀{n} → List (Fin n) → Subset n
  finList-to-set [] = ∅
  finList-to-set (x ∷ x₁) = finList-to-set x₁ [ x ]≔ true


  filter-mono : ∀ {a} {A : Set a} (p : A → Bool) → (q : A → Bool) → ((x : A) → T (p x) → T (q x)) → (xs ys : List A) → xs list⊆ ys → filter p xs list⊆ filter q ys
  filter-mono p q imp xs ys xs⊆ys {x} x∈filter-xs with filter-∈′ p xs x∈filter-xs
  filter-mono p q imp xs ys xs⊆ys {x} x∈filter-xs | x∈xs , px = let qx = imp x (Equivalence.from (T-≡) ⟨$⟩ px) in filter-∈ q ys (xs⊆ys x∈xs) (Equivalence.to T-≡ ⟨$⟩ qx) 

  toFinList-monotone : ∀{n} → Monotone₂ (_setFin⊆_ {n = n}) _list⊆_ toFinList
  toFinList-monotone {n} {a} {b} x {x₁} x₂ = filter-mono (λ y → ⌊ y ∈? a ⌋) (λ y → ⌊ y ∈? b ⌋) (λ x₃ x₄ → fromWitness (x (toWitness x₄))) (Data.Vec.toList (allFin n)) (Data.Vec.toList (allFin n)) (λ x₄ → x₄) x₂ 

  toFinList-⊆ : ∀{n} → {a : Fin n} {s : Subset n} → a setFin∈ s → a list∈ (toFinList s)
  toFinList-⊆ x = filter-∈ (λ y → ⌊ y ∈? _ ⌋) (Data.Vec.toList (allFin _)) (∈⇒List-∈ (∈-allFin _)) (Equivalence.to T-≡ ⟨$⟩ fromWitness x)

  list∈-to-setFin∈ : ∀{n} → {a : Fin n} {s : Subset n} →  a list∈ (toFinList s) → a setFin∈ s
  list∈-to-setFin∈ {n} {a} {s} x = ∀-elim (λ x → x setFin∈ s) (Data.List.filter (λ y → ⌊ y ∈? s ⌋) (Data.Vec.toList (allFin n))) (filter-filters (λ x → x setFin∈ s) (λ x₁ → x₁ ∈? s) (Data.Vec.toList (allFin n))) a x 
  
  module Containment {a} {n : ℕ} { A : Set a} (fin↔ : A ↔ Fin n) where
   
    infix 4 _set∈_ _set∈?_ _set⊆_
    _set∈_ : (a : A) → Subset n → Set 
    a set∈ b = (Inverse.to fin↔ ⟨$⟩ a) setFin∈ b
    
    _set∉_ : (a : A) → Subset n → Set 
    a set∉ b = ¬ a set∈ b 
  
    _set∈?_ : (a : A) → (p : Subset n) → Dec (a set∈ p)
    a set∈? b = Inverse.to fin↔ ⟨$⟩ a ∈? b

    _set⊆_ : Subset n → Subset n → Set a
    xs set⊆ ys = ∀ {x} → x set∈ xs → x set∈ ys

    list∈-≡ : {a b : A} {s : List A} (p : a ≡ b) → a list∈ s → b list∈ s
    list∈-≡{a₁} {.a₁} {s} refl q = q

    
    setFin∈-≡ : {a b : Fin n} {s : Subset n} (p : a ≡ b) → a setFin∈ s → b setFin∈ s
    setFin∈-≡ refl x = x
    
    set∈-≡ : {a b : A} {s : Subset n} (p : a ≡ b) → a set∈ s → b set∈ s
    set∈-≡ refl x = x
    
    set⊆-to-setFin⊆ : {a b : Subset n} → a set⊆ b → a setFin⊆ b
    set⊆-to-setFin⊆ {a} {b} x {x₁} x₂ = setFin∈-≡ (Inverse.right-inverse-of fin↔ x₁) (x (setFin∈-≡ (sym (Inverse.right-inverse-of fin↔ x₁)) x₂))

    set-to-list : Subset n → List A
    set-to-list x = Data.List.map (λ x → Inverse.from fin↔ ⟨$⟩ x) (toFinList x)

    list-to-set : List A → Subset n
    list-to-set x = finList-to-set (Data.List.map (λ x → Inverse.to fin↔ ⟨$⟩ x) x)
  
    set-to-list-mono : Monotone₂ _set⊆_ _list⊆_ set-to-list
    set-to-list-mono x {x₁} x₂ = map-mono (λ x → Inverse.from fin↔ ⟨$⟩ x) (toFinList-monotone (λ x₄ → set⊆-to-setFin⊆ x x₄)) x₂


    setFin∈-to-listFin∈ : {a : Fin n} → {s : Subset n } → a setFin∈ s → (Inverse.from fin↔ ⟨$⟩ a) list∈ set-to-list s
    setFin∈-to-listFin∈ {a} {s} p = Inverse.to map-∈↔ ⟨$⟩ (a , ((toFinList-⊆ {n} {a} {s} p) , refl))

    set∈-to-list∈ : {a : A} → {s : Subset n } → a set∈ s → a list∈ set-to-list s
    set∈-to-list∈ {a} {s} x = list∈-≡ (Inverse.left-inverse-of fin↔ a) (setFin∈-to-listFin∈ x) 
    

    listFin∈-to-setFin∈ : {a : Fin n} → {s : Subset n } → (Inverse.from fin↔ ⟨$⟩ a) list∈ set-to-list s → a setFin∈ s
    listFin∈-to-setFin∈ {a} {s} p = let (b , c , d) = Inverse.from map-∈↔ ⟨$⟩ p
                                        r = Inverse.right-inverse-of fin↔ a
                                        z = list∈-to-setFin∈ c
                                    in setFin∈-≡ (sym (trans (sym r) (trans (cong (λ a → Inverse.to fin↔ ⟨$⟩ a) d) (Inverse.right-inverse-of fin↔ _)))) z 
    
    list∈-to-set∈ : {a : A} → {s : Subset n } → a list∈ set-to-list s → a set∈ s
    list∈-to-set∈ {a} {s} x = listFin∈-to-setFin∈ (list∈-≡ (sym (Inverse.left-inverse-of fin↔ a)) x)
  

    ⊔⇔⊎ : {x : A} → {a b : Subset n} → x set∈ (a ∪ b) ⇔ (x set∈ a ⊎ x set∈ b)
    ⊔⇔⊎ = ⊔⇔⊎-fin

    ⊓⇔× : {p₁ p₂ : Subset n} {x : A} → x set∈ p₁ ∩ p₂ ⇔ (x set∈ p₁ × x set∈ p₂)
    ⊓⇔× = ⊓⇔×-fin


    set∉-right : {X Y : Subset n} {x : A} → x set∈ X ∪ Y → x set∉ Y → x set∈ X
    set∉-right x₁ x₂ = setFin∉-right x₁ x₂

    set∉-left : {X Y : Subset n} {x : A} → x set∈ X ∪ Y → x set∉ X → x set∈ Y
    set∉-left x₁ x₂ = setFin∉-left x₁ x₂


    set∈-- : { a b : Subset n} → {x : A} → x set∈ a → x set∉ b → x set∈ a - b
    set∈-- = setFin∈--


    ¬∁ : {a : Subset n} → {x : A} → ¬ x set∈ ∁ a → x set∈ a
    ¬∁ = setFin¬∁
    
    set∈∁⇒set∉ : {a : Subset n} → {x : A} → x set∈ ∁ a → ¬ x set∈ a
    set∈∁⇒set∉ = setFin∈∁⇒setFin∉

    set∈-cong₂ : {a b : A} → {c d : Subset n} → a ≡ b → c ≡ d → a set∈ c → b set∈ d
    set∈-cong₂ refl refl x₂ = x₂

