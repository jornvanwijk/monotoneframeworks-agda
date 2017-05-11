open import Relation.Binary.PropositionalEquality

module MaybeProp 
  (funext : {X : Set}{Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g) where

open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Nullary
open import Data.List
open import Utilities
open import Coinduction
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Sum renaming (_⊎_ to _+_) hiding (map)
open import Data.Empty
open import Function
open import Data.Bool
open import Data.Unit hiding (_≤_)
open import Noetherian
open import NoethRels
open import Listable
open import Bounded

MaybePropBounded : (X : Set) → isProp X → Bounded (⊤ + X)
MaybePropBounded X p = 3 ,
  (λ { [] () ; (x ∷ []) (s≤s ()) ;
       (x ∷ x₁ ∷ []) (s≤s (s≤s ())) ;
       (inj₁ tt ∷ inj₁ tt ∷ x₂ ∷ xs) x₃ → duphere (here refl) ;
       (inj₁ tt ∷ inj₂ y ∷ inj₁ tt ∷ xs) x₃ → duphere (there (here refl)) ;
       (inj₁ tt ∷ inj₂ y ∷ inj₂ y₁ ∷ xs) x₃ → dupthere (duphere (here (cong inj₂ p))) ;
       (inj₂ y ∷ inj₁ tt ∷ inj₁ tt ∷ xs) x₃ → dupthere (duphere (here refl)) ;
       (inj₂ y ∷ inj₁ tt ∷ inj₂ y₁ ∷ xs) x₃ → duphere (there (here (cong inj₂ p))) ;
       (inj₂ y ∷ inj₂ y₁ ∷ x₂ ∷ xs) x₃ → duphere (here (cong inj₂ p)) })

NoethExpose→ListableM : (∀ X → isProp X → NoethExpose (⊤ + X))
  → ∀ X → isProp X → Listable (⊤ + X)
NoethExpose→ListableM ne X p = NoethExpose→Listable (inj₁ tt) (ne X p)

MDec' : ∀ X → isProp X → (xs : List (⊤ + X))
  → (Σ[ x ∈ X ] inj₂ x ∈ xs) + (∀ x → x ∈ xs → x ≡ inj₁ tt)
MDec' X p [] = inj₂ (λ x → λ ())
MDec' X p (inj₁ tt ∷ xs) with MDec' X p xs
MDec' X p (inj₁ tt ∷ xs) | inj₁ (x , q) = inj₁ (x , there q)
MDec' X p (inj₁ tt ∷ xs) | inj₂ f = inj₂ (λ { .(inj₁ tt) (here refl) → refl ; x (there p) → f x p })
MDec' X p (inj₂ xp ∷ xs) = inj₁ (xp , here refl)  


MDec : ∀ X → isProp X → Listable (⊤ + X) → X + ¬ X
MDec X p (xs , l) with MDec' X p xs
MDec X p (xs , l) | inj₁ (q , ixs) = inj₁ q
MDec X p (xs , l) | inj₂ f = inj₂ (λ c → g (f (inj₂ c) (l (inj₂ c))))
  where
    g : {X Y : Set}{x : X}{y : Y} → inj₂ y ≡ inj₁ x → ⊥
    g ()


MaybePropNoethExpose→LEM : (∀ X → isProp X → NoethExpose (⊤ + X))
  → ∀ X → isProp X → X + ¬ X
MaybePropNoethExpose→LEM ne X p = MDec X p (NoethExpose→ListableM ne X p)

