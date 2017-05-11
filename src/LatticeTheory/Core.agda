module LatticeTheory.Core where

import Algebra
import Level
open import Algebra.Properties.Lattice renaming (poset to poset')
open import Algebra.Structures
open import Data.Product renaming (_×_ to _⋀_)
open import Function
open import Relation.Binary 
open import Relation.Binary.Properties.Poset renaming (strictPartialOrder to strictPartialOrder')
open import Relation.Nullary
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality renaming (decSetoid to decSetoid') hiding (setoid)
open import Data.Empty renaming (⊥ to Empty-⊥)
import Relation.Binary.NonStrictToStrict
import Algebra.FunctionProperties
open import Relation.Nullary.Decidable
open import Data.List
open import Data.Bool hiding (_≟_ ; decSetoid)
open import Monotonicity

module Operators {a} (ℂ : Set a) (⊥ : ℂ) (open Algebra.FunctionProperties {a} {_} {ℂ} _≡_) (_⊔_ : Op₂ ℂ) (_≟_ : Decidable {A = ℂ} _≡_) where

  -- todo add ⋢,⋣
  infix 5 _⊑_ 
  infix 5 _⊑?_
  infix 5 _⊏_ 
  infix 5 _⊏?_
  infix 5 _⊒_ 
  infix 5 _⊒?_
  infix 5 _⊐_ 
  infix 5 _⊐?_

  
  _⊑_ : Rel ℂ _
  _⊑_ = λ x y → (x ⊔ y) ≡ y

  _⊑?_ : Decidable _⊑_
  _⊑?_ = λ x y → (x ⊔ y) ≟ y

  open Relation.Binary.NonStrictToStrict _≡_ _⊑_ using (_<_) -- renaming (_<_ to _⊏_) explicit definition so that we can set fixity.
  open Relation.Binary.NonStrictToStrict _≡_ _⊑_ using (decidable)

  _⊏_ : Rel ℂ _
  _⊏_ = _<_
  

  _⊐_ : Rel ℂ _
  _⊐_ = flip _⊏_
  
  _⊒_ : Rel ℂ _
  _⊒_ = flip _⊑_
  
  _⊒?_ : Decidable _⊒_
  _⊒?_ = flip _⊑?_
  
  _⊏?_ : Decidable _⊏_
  _⊏?_ = decidable _≟_ _⊑?_
  
  _⊐?_ : Decidable _⊐_
  _⊐?_ = flip _⊏?_

  infixr 6 ⨆
  ⨆ : List ℂ → ℂ
  ⨆ = foldr _⊔_ ⊥  

  module Properties (⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c) (⊔-idem : Idempotent _⊔_) (⊔-comm : Commutative _⊔_) (⊔-cong₂ : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_) (⊔-assoc : Associative _⊔_)  where
    module _ where
      open ≡-Reasoning
      ⊑-trans : Transitive _⊑_
      ⊑-trans {i} {j} {k} i⊔j≡j j⊔k≡k = begin
                                i ⊔ k ≡⟨ ⊔-cong₂ refl (sym j⊔k≡k) ⟩ 
                                i ⊔ (j ⊔ k) ≡⟨ sym (⊔-assoc i j k) ⟩
                                (i ⊔ j) ⊔ k ≡⟨ ⊔-cong₂ i⊔j≡j refl ⟩  
                                j ⊔ k ≡⟨ j⊔k≡k ⟩
                                k ∎
     

      ⊑-reflexive : Reflexive _⊑_
      ⊑-reflexive = ⊔-idem _
    
      ⊑-antisym : Antisymmetric _≡_ _⊑_ 
      ⊑-antisym {x} {y} x⊔y≡y y⊔x≡x = begin
                                x
                                ≡⟨ sym y⊔x≡x ⟩
                                (y ⊔ x)
                                ≡⟨ ⊔-comm y x ⟩
                                (x ⊔ y)
                                ≡⟨ x⊔y≡y ⟩
                                y ∎ 

      ⊔-on-⊑ : {a b c d : ℂ} → a ⊑ b → c ⊑ d → (a ⊔ c) ⊑ (b ⊔ d)
      ⊔-on-⊑ {a} {b} {c} {d} x x₁ = begin
                     (a ⊔ c) ⊔ (b ⊔ d)
                     ≡⟨ sym (⊔-assoc (a ⊔ c) b d) ⟩
                     (((a ⊔ c) ⊔ b) ⊔ d)
                     ≡⟨ cong (\x → x ⊔ d) (⊔-assoc a c b) ⟩
                     ((a ⊔ (c ⊔ b)) ⊔ d)
                     ≡⟨ cong (\x → (a ⊔ x) ⊔ d) (⊔-comm c b) ⟩
                     ((a ⊔ (b ⊔ c)) ⊔ d)
                     ≡⟨ cong (\x → x ⊔ d) (sym (⊔-assoc a b c)) ⟩
                     (((a ⊔ b) ⊔ c) ⊔ d)
                     ≡⟨ cong (\y → (y ⊔ c) ⊔ d) x ⟩
                     ((b ⊔ c) ⊔ d)
                     ≡⟨ ⊔-assoc b c d ⟩
                     ((b ⊔ (c ⊔ d)))
                     ≡⟨ cong (\y → b ⊔ y) x₁ ⟩
                     (b ⊔ d) ∎

      ⊔-on-left-⊑ : {a b c : ℂ} → a ⊑ c → b ⊑ c  → a ⊔ b ⊑ c
      ⊔-on-left-⊑ {a} {b} {c} p q = begin
                                     (a ⊔ b) ⊔ c ≡⟨ ⊔-assoc _ _ _ ⟩ 
                                     a ⊔ (b ⊔ c) ≡⟨ (cong (\w → a ⊔ w) q) ⟩ 
                                     a ⊔ c ≡⟨ p ⟩ 
                                     c ∎
                                     
      ⊔-on-right-⊑ : {a b c : ℂ} → a ⊑ b → a ⊑ b ⊔ c
      ⊔-on-right-⊑ {a} {b} {c} p = begin
                                   a ⊔ (b ⊔ c)
                                   ≡⟨ sym (⊔-assoc _ _ _) ⟩
                                   (a ⊔ b) ⊔ c
                                   ≡⟨ cong (_⊔ c) p ⟩
                                   b ⊔ c
                                   ∎
                                   
      ⊔-on-right-⊑′ : {a b c : ℂ} → a ⊑ c → a ⊑ b ⊔ c
      ⊔-on-right-⊑′ {a} {b} {c} p = begin
                                   a ⊔ (b ⊔ c)
                                   ≡⟨ cong (_⊔_ a) (⊔-comm _ _) ⟩ 
                                   a ⊔ (c ⊔ b)
                                   ≡⟨ sym (⊔-assoc _ _ _) ⟩
                                   (a ⊔ c) ⊔ b
                                   ≡⟨ cong (_⊔ b) p ⟩
                                   c ⊔ b
                                   ≡⟨ ⊔-comm _ _ ⟩
                                   b ⊔ c
                                   ∎
                                   
      ⊑-split-left :  {a b c : ℂ} → a ⊔ b ⊑ c → a ⊑ c
      ⊑-split-left {a} {b} {c} x = 
        begin
        (a ⊔ c)
        ≡⟨ cong (_⊔_ a) (sym x) ⟩
        (a ⊔ ((a ⊔ b) ⊔ c))
        ≡⟨ sym (⊔-assoc a (a ⊔ b) c) ⟩
        ((a ⊔ (a ⊔ b)) ⊔ c)
        ≡⟨ cong (_⊔ c) (sym (⊔-assoc a a b)) ⟩
        (((a ⊔ a) ⊔ b) ⊔ c)
        ≡⟨ cong (λ x → (x ⊔ b) ⊔ c) (⊔-idem _) ⟩
        (a ⊔ b) ⊔ c
        ≡⟨ x ⟩
        c
        ∎
        
      ⊑-split-right :  {a b c : ℂ} → a ⊔ b ⊑ c → b ⊑ c
      ⊑-split-right {a} {b} {c} x = 
        begin
        (b ⊔ c)
        ≡⟨ cong (_⊔_ b) (sym x) ⟩
        (b ⊔ ((a ⊔ b) ⊔ c))
        ≡⟨ sym (⊔-assoc b (a ⊔ b) c) ⟩
        ((b ⊔ (a ⊔ b)) ⊔ c)
        ≡⟨ cong (_⊔ c) (cong (_⊔_ b) (⊔-comm a b)) ⟩
        ((b ⊔ (b ⊔ a)) ⊔ c) 
        ≡⟨ cong (_⊔ c) (sym (⊔-assoc b b a)) ⟩
        (((b ⊔ b) ⊔ a) ⊔ c)
        ≡⟨ cong (λ x → (x ⊔ a) ⊔ c) (⊔-idem _) ⟩
        ((b ⊔ a) ⊔ c)
        ≡⟨ cong (_⊔ c) (⊔-comm _ _) ⟩
        (a ⊔ b) ⊔ c
        ≡⟨ x ⟩
        c
        ∎
                                     
      ⊔-on-right-⊒ : {a b c : ℂ} → a ⊒ b → a ⊒ c → a ⊒ b ⊔ c
      ⊔-on-right-⊒ {a} {b} {c} p q = begin
                                     (b ⊔ c) ⊔ a ≡⟨ ⊔-assoc _ _ _ ⟩
                                     b ⊔ (c ⊔ a) ≡⟨ cong (\y → b ⊔ y) q ⟩ 
                                     (b ⊔ a) ≡⟨ p ⟩ 
                                     a ∎ 
                                     
      right-⊔-on-⊑ : {a b : ℂ} → a ⊑ (b ⊔ a)
      right-⊔-on-⊑ {a} {b} = begin
                              a ⊔ (b ⊔ a)
                              ≡⟨ cong (_⊔_ a) (⊔-comm _ _) ⟩
                              a ⊔ (a ⊔ b)
                              ≡⟨ sym (⊔-assoc _ _ _) ⟩
                              (a ⊔ a) ⊔ b
                              ≡⟨ cong (_⊔ b) (⊔-idem _) ⟩
                              a ⊔ b
                              ≡⟨ ⊔-comm _ _ ⟩
                              (b ⊔ a)
                              ∎
                              
      right-⊔-on-⊑' : {a b c : ℂ} → a ≡ c → a ⊑ (b ⊔ c)
      right-⊔-on-⊑' {a} {b} {c} refl = begin
                              a ⊔ (b ⊔ a)
                              ≡⟨ cong (_⊔_ a) (⊔-comm _ _) ⟩
                              a ⊔ (a ⊔ b)
                              ≡⟨ sym (⊔-assoc _ _ _) ⟩
                              (a ⊔ a) ⊔ b
                              ≡⟨ cong (_⊔ b) (⊔-idem _) ⟩
                              a ⊔ b
                              ≡⟨ ⊔-comm _ _ ⟩
                              (b ⊔ a)
                              ∎
                              
      left-⊔-on-⊑ : {a b : ℂ} → a ⊑ (a ⊔ b)
      left-⊔-on-⊑ {a} {b} = begin
                             a ⊔ (a ⊔ b)
                             ≡⟨ sym (⊔-assoc _ _ _) ⟩
                             (a ⊔ a) ⊔ b
                             ≡⟨ cong (_⊔ b) (⊔-idem a) ⟩
                             a ⊔ b ∎
                             
      left-⊔-on-⊑' : {a b c : ℂ} → a ≡ c → a ⊑ (c ⊔ b)
      left-⊔-on-⊑' {a} {b} {c} refl = begin
                             a ⊔ (a ⊔ b)
                             ≡⟨ sym (⊔-assoc _ _ _) ⟩
                             (a ⊔ a) ⊔ b
                             ≡⟨ cong (_⊔ b) (⊔-idem a) ⟩
                             a ⊔ b ∎ 


      ⊑-cong : (f : ℂ → ℂ) → (Monotone _⊑_ f) → {a b : ℂ} → a ⊑ b → f a ⊑ f b 
      ⊑-cong f x p = x p

      ≡⇒⊑ : {a b : ℂ} → a ≡ b → a ⊑ b
      ≡⇒⊑ refl = ⊔-idem _

      open import Relation.Nullary.Negation
      ⋢⇒≢ : {a b : ℂ} → ¬ (a ⊑ b) → ¬ a ≡ b
      ⋢⇒≢ = contraposition ≡⇒⊑

      ¬a⊏a : {a : ℂ} → ¬ (a ⊏ a)
      ¬a⊏a (proj₃ , proj₄) = proj₄ (trans (sym proj₃) proj₃)

      ¬⊐∧⊑⇒≡ : {a b : ℂ} → ¬ (a ⊏ b) → a ⊑ b → a ≡ b
      ¬⊐∧⊑⇒≡ {a} {b} x x₁ = decidable-stable (a ≟ b) (λ x₂ → ⊥-elim (x (x₁ , x₂))) 

      {-
      -- cannot prove this without additional selective constraint. i.e. a ⊔ b ≡ a  ∨ a ⊔ b ≡ b
      ⋢⇒⊐ : {a b : ℂ} → ¬ (a ⊑ b) → a ⊐ b
      ⋢⇒⊐ {a} {b} p with a ⊐? b
      ⋢⇒⊐ {a} {b} p | yes q = q
      ⋢⇒⊐ {a} {b} p | no ¬q = {!!} , (λ x → p (sym (trans (sym (⊔-idem _)) (cong (_⊔ b) x)))) -- decidable-stable (a ⊐? b) (λ x → ⊥-elim (p {!!})) -- {!!} , (λ{ refl → x (⊔-idem _)})
      -}
      
      ⊔-monotone-right : {x : ℂ} → Monotone _⊑_ (_⊔ x)
      ⊔-monotone-right {x} {x₁} {y} x₂ = ⊔-on-⊑ x₂ ⊑-reflexive
      
      ⊔-monotone-left : {x : ℂ} → Monotone _⊑_ (_⊔_ x)
      ⊔-monotone-left {x} {x₁} {y} x₂ = ⊔-on-⊑ ⊑-reflexive x₂

    open Relation.Binary.NonStrictToStrict _≡_ _⊑_ public using () renaming (<-resp-≈ to ⊏-resp-≡; irrefl to ⊏-irrefl)
    open Relation.Binary.NonStrictToStrict _≡_ _⊑_ using (antisym⟶asym) renaming (trans to ⊏-trans')

    ⊏-asymmetric : Asymmetric _⊏_
    ⊏-asymmetric = antisym⟶asym ⊑-antisym

    ⊐-asymmetric : Asymmetric _⊐_
    ⊐-asymmetric = ⊏-asymmetric

    decPoset : DecPoset a a a
    decPoset = record
     { Carrier = ℂ
     ; _≈_ = _≡_
     ; _≤_ = _⊑_
     ; isDecPartialOrder = record
      { isPartialOrder = record
       { isPreorder = record
        { isEquivalence = isEquivalence
        ; reflexive = λ{refl → ⊑-reflexive}
        ; trans = ⊑-trans
        }
       ; antisym = ⊑-antisym
      }
      ; _≟_ = _≟_
      ; _≤?_ = _⊑?_
      }
     }     
    open DecPoset decPoset public using (poset ; module Eq)
    open Eq public using (setoid ; decSetoid)
     
    open IsDecPartialOrder (DecPoset.isDecPartialOrder decPoset) using (isPartialOrder)
    ⊏-trans : Transitive _⊏_
    ⊏-trans = ⊏-trans' isPartialOrder
    
    ⊐-trans : Transitive _⊐_
    ⊐-trans = λ x x₁ → ⊏-trans x₁ x
      
    module Reasoning where
      record ReasoningOperator (_●_ : Rel ℂ a) : Set a where
       constructor reasoningOperator
       field     
         p : _≡_ ⇒ _●_
  
      infix  3 _∎
      _∎ : {_●_ : Rel ℂ a} → ⦃ p : ReasoningOperator _●_ ⦄ → (x : ℂ) → x ● x
      _∎ ⦃ reasoningOperator p ⦄ _ = p refl
      
      infixr 2 _≡⟨_⟩_
      _≡⟨_⟩_ :  {_●_ : Rel ℂ a} → ⦃ p : ReasoningOperator _●_ ⦄ → (x : ℂ) → {y z : ℂ} → x ≡ y → y ● z → x ● z
      _≡⟨_⟩_ ⦃ reasoningOperator p ⦄ _ refl x₂ = x₂
   
      infix 1 begin_
      begin_ : ∀{x y : ℂ} → x ≡ y → x ≡ y
      begin_ x≡y = x≡y
  
      infixr 2 _≡⟨⟩_
      _≡⟨⟩_ :{_●_ : Rel ℂ a} → ⦃ p : ReasoningOperator _●_ ⦄ → ∀ (x {y} : ℂ) → x ● y → x ● y
      _ ≡⟨⟩ x≡y = x≡y

      infixr 2 _⊑⟨_⟩_ 

      _⊑⟨_⟩_ : (x : ℂ) → {y z : ℂ} → x ⊑ y → y ⊑ z → x ⊑ z
      _⊑⟨_⟩_ x {y} {z} x₁ x₂ = ⊑-trans x₁ x₂

  
      instance
        ⊑-reasoning : ReasoningOperator _⊑_
        ⊑-reasoning = reasoningOperator (λ where refl → ⊑-reflexive)
        
      instance 
        ≡-reasoning : ReasoningOperator _≡_ 
        ≡-reasoning = reasoningOperator id

                   
    open import Data.List.Any
    open Membership setoid renaming (_∈_ to _list∈_ ; _⊆_ to _list⊆_)
    open Reasoning
    open import Data.List.Properties

    private
      -- ≡ proofs get lifted to ⊑.    
      example⊑ : ∀{a b c x z} → a ⊑ b → b ⊑ c → x ≡ a → c ≡ z → x ⊑ z
      example⊑ {a} {b} {c} {x} {z} x₁ x₂ x₃ x₄ =
        begin x ≡⟨ x₃ ⟩ -- ⇒ x ⊑ a
              a ⊑⟨ x₁ ⟩
              b ⊑⟨ x₂ ⟩
              c ≡⟨ x₄ ⟩ -- ⇒ c ⊑ z
              z ∎
  
      example≡ : ∀{a b c d} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
      example≡ {a} {b} {c} {d} x₁ x₂ x₃ =
        begin a ≡⟨ x₁ ⟩
              b ≡⟨ x₂ ⟩
              c ≡⟨ x₃ ⟩
              d ∎

    x⊑⨆x : (x : ℂ) → (xs : List ℂ) → x list∈ xs → x ⊑ ⨆ xs
    x⊑⨆x x [] ()
    x⊑⨆x .x (x ∷ xs) (here refl) rewrite sym (⊔-assoc x x (⨆ xs)) = cong (\y → y ⊔ (⨆ xs)) (⊔-idem x)
    x⊑⨆x x (x₁ ∷ xs) (there p) = begin
                                  (x
                                  ⊑⟨ x⊑⨆x x xs p ⟩
                                  ⨆ xs ⊑⟨ right-⊔-on-⊑ ⟩
                                  x₁ ⊔ (⨆ xs) ≡⟨⟩ 
                                  ⨆ (x₁ ∷ xs) ∎)


    ⊑⨆x : (x : ℂ) → (xs : List ℂ) → Any (_⊑_ x) xs → x ⊑ ⨆ xs
    ⊑⨆x x [] ()
    ⊑⨆x x (x₁ ∷ xs) (here px) = ⊔-on-right-⊑ px
    ⊑⨆x x (x₁ ∷ xs) (there x₂) = ⊔-on-right-⊑′ (⊑⨆x x xs x₂)


    open import Data.List.All
    open import Data.List.Any
    x⊒⨆' : (x : ℂ) → (xs : List ℂ) → ((y : ℂ) → y list∈ xs → x ⊒ y) → x ⊒ ⨆ xs
    x⊒⨆' x [] f = ⊥-isMinimal x
    x⊒⨆' x (x₁ ∷ xs) f = ⊔-on-right-⊒ (f x₁ (here refl)) (x⊒⨆' x xs (λ y x₂ → f y (there x₂)))

    x⊒⨆ : (x : ℂ) → (xs : List ℂ) → All (\y → x ⊒ y) xs → x ⊒ ⨆ xs
    x⊒⨆ x .[] [] = ⊥-isMinimal x
    x⊒⨆ x₁ .(_ ∷ _) (px ∷ x₂) = ⊔-on-right-⊒ px (x⊒⨆ x₁ _ x₂)

    
    open import Monotonicity
    open import Util.Subset
    ⨆-mono : Monotone₂ _list⊆_ _⊑_ ⨆
    ⨆-mono x = x⊒⨆' _ _ (λ y x₁ → x⊑⨆x _ _ (x x₁)) 

    import Relation.Binary.List.Pointwise as Pointwise
    ⨆≡⨆ : {xs ys : List ℂ} → xs ≡ ys → ⨆ xs ≡ ⨆ ys
    ⨆≡⨆ {xs} {.xs} refl = refl
    

    ⨆⊑⨆-pointwise : (xs ys : List ℂ) → Pointwise.Rel _⊑_ xs ys → ⨆ xs ⊑ ⨆ ys
    ⨆⊑⨆-pointwise .[] .[] Pointwise.[] = ⊥-isMinimal _
    ⨆⊑⨆-pointwise .(x ∷ xs) .(y ∷ ys) (Pointwise._∷_ {x} {xs} {y} {ys} x⊑y ps) =
      begin
      (x ⊔ ⨆ xs) ⊔ (y ⊔ ⨆ ys) ≡⟨ cong (_⊔_ (x ⊔ ⨆ xs)) (⊔-comm y (⨆ ys)) ⟩
      (x ⊔ ⨆ xs) ⊔ (⨆ ys ⊔ y) ≡⟨ sym (⊔-assoc (x ⊔ ⨆ xs) (⨆ ys) y) ⟩
      (((x ⊔ ⨆ xs) ⊔ ⨆ ys) ⊔ y) ≡⟨ cong (_⊔ y) (⊔-assoc x (⨆ xs) (⨆ ys)) ⟩
      (x ⊔ ((⨆ xs ⊔ ⨆ ys))) ⊔ y ≡⟨ cong (_⊔ y ) (cong (_⊔_ x) (⨆⊑⨆-pointwise _ _ ps )) ⟩
      (x ⊔ ⨆ ys) ⊔ y ≡⟨ ⊔-assoc _ _ _ ⟩
      x ⊔ (⨆ ys ⊔ y) ≡⟨ cong (_⊔_ x) (⊔-comm _ _) ⟩
      x ⊔ (y ⊔ ⨆ ys) ≡⟨ (sym (⊔-assoc _ _ _)) ⟩
      (x ⊔ y) ⊔ ⨆ ys ≡⟨ cong (_⊔ ⨆ ys) x⊑y ⟩
      y ⊔ ⨆ ys ∎


    ⊔-over-⊔ : ∀{a b c d} → (a ⊔ b) ⊔ (c ⊔ d) ≡ (a ⊔ c) ⊔ (b ⊔ d)
    ⊔-over-⊔ {a} {b} {c} {d} = begin
                                (a ⊔ b) ⊔ (c ⊔ d)
                                ≡⟨ sym (⊔-assoc _ _ _) ⟩
                                ((a ⊔ b) ⊔ c) ⊔ d
                                ≡⟨ cong (_⊔ d) (⊔-assoc _ _ _) ⟩
                                (a ⊔ (b ⊔ c)) ⊔ d
                                ≡⟨ cong (_⊔ d) (cong (_⊔_ a) (⊔-comm _ _)) ⟩
                                (a ⊔ (c ⊔ b)) ⊔ d
                                ≡⟨ cong (_⊔ d) (sym (⊔-assoc _ _ _)) ⟩
                                ((a ⊔ c) ⊔ b) ⊔ d
                                ≡⟨ ⊔-assoc _ _ _ ⟩
                                (a ⊔ c) ⊔ (b ⊔ d)
                                ∎
                                
    ⊔-rotate-left : ∀{a b c} → a ⊔ (b ⊔ c) ≡ (a ⊔ c) ⊔ b
    ⊔-rotate-left {a} {b} {c} = begin
                                a ⊔ (b ⊔ c)
                                ≡⟨ cong (_⊔_ a) (⊔-comm _ _) ⟩
                                a ⊔ (c ⊔ b)
                                ≡⟨ sym (⊔-assoc a c b) ⟩ 
                                (a ⊔ c) ⊔ b
                                ∎
                                
    ⊔-rotate-right : ∀{a b c} → (a ⊔ b) ⊔ c ≡ b ⊔ (a ⊔ c)
    ⊔-rotate-right {a} {b} {c} = begin
                                 (a ⊔ b) ⊔ c
                                 ≡⟨ cong (_⊔ c) (⊔-comm _ _) ⟩
                                 (b ⊔ a) ⊔ c
                                 ≡⟨ ⊔-assoc _ _ _ ⟩ 
                                 b ⊔ (a ⊔ c)
                                 ∎

    x∈⨆ : (x : ℂ) → (xs : List ℂ) → x list∈ xs → x ⊔ ⨆ xs ≡ ⨆ xs
    x∈⨆ x [] ()
    x∈⨆ .x₁ (x₁ ∷ xs) (here refl) = trans (sym (⊔-assoc x₁ x₁ (foldr _⊔_ ⊥ xs))) (cong (_⊔ foldr _⊔_ ⊥ xs) (⊔-idem x₁))
    x∈⨆ x (x₁ ∷ xs) (there x₂) = trans (sym ⊔-rotate-right) (trans (⊔-assoc _ _ _) (cong (_⊔_ x₁ ) (x∈⨆ x xs x₂)))


{-
The greatest lower bound of a set X, glb(X), also has an impredicative definition: y = glb(X) if and only if for all elements x of X, y is less than or equal to x, and any z less than or equal to all elements of X is less than or equal to y. But this definition also quantifies over the set (potentially infinite, depending on the order in question) whose members are the lower bounds of X, one of which being the glb itself. Hence predicativism would reject this definition.
https://en.wikipedia.org/wiki/Impredicativity

Agda is a predicative system; thus directed join. 
-}
record BoundedSemiLattice a : Set (Level.suc a) where
  constructor completeLattice
  infixr 7 _⊔_
  infix 4 _≟_
  field
    ℂ         : Set a       -- Carrier type
  open Algebra.FunctionProperties {a} {_} {ℂ} _≡_ 
  field
    _⊔_       : Op₂ ℂ       -- Binary join
    _≟_       : Decidable {A = ℂ} _≡_
    ⊥         : ℂ           -- Least element
  open Operators ℂ ⊥ _⊔_ _≟_ public
  field
    ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c    -- Proof that ⊥ is the least element
    ⊔-idem        : Idempotent _⊔_
    ⊔-comm        : Commutative _⊔_
    ⊔-cong₂       : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
    ⊔-assoc       : Associative _⊔_
  open Properties ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong₂ ⊔-assoc public
  field
    ⊐-isWellFounded : Well-founded _⊐_ -- Ascending chain condition

{- to make displaying nicer -}
_⊔′_ : ∀{a} → {r : BoundedSemiLattice a} → BoundedSemiLattice.ℂ r → BoundedSemiLattice.ℂ r → BoundedSemiLattice.ℂ r 
_⊔′_ {_} {r} a b = BoundedSemiLattice._⊔_ r a b
{-# DISPLAY BoundedSemiLattice._⊔_ x y z = y ⊔′ z #-} 

⨆′ : ∀{a} → {r : BoundedSemiLattice a} → List (BoundedSemiLattice.ℂ r) → BoundedSemiLattice.ℂ r
⨆′ {_} {r} a = BoundedSemiLattice.⨆ r a
{-# DISPLAY BoundedSemiLattice.⨆ r xs = ⨆′ xs #-}

⊥′ : ∀{a} → {r : BoundedSemiLattice a} → BoundedSemiLattice.ℂ r
⊥′ {_} {r} = BoundedSemiLattice.⊥ r
{-# DISPLAY BoundedSemiLattice.⊥ r = ⊥′ #-}

