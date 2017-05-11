

module Utilities.ListMonad where

open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Utilities.ListProperties
open import Data.Product
open import Data.List renaming (_++_ to _+++_)
open import Data.Sum


-- `bind`
_>>=_ : {A B : Set} → List A → (A → List B) → List B
_>>=_ l f = foldl (λ res el →  res ++ f el) [] l

-- `unit`
return : {A : Set} → A → List A
return a = [ a ]


>>=split : {A B : Set} → (a b : List A) → (f : A → List B)
 →  (a ++ b) >>= f ≡ (a >>= f) ++ (b >>= f) 
>>=split [] b f = refl
>>=split (x ∷ a) b f rewrite foldl-unf (f x) (a ++ b) f 
 | foldl-unf (f x) a f 
 | sym (++-assoc (f x) (a >>= f) (b >>= f)) 
 | >>=split a b f = refl

{- monad laws-}

-- left identity
left-id-law :  {A B : Set} →  (a : A) →  (f : A → List B)
  → return a >>= f ≡  f a
left-id-law a f = refl 

-- right identity
right-id-law : {A : Set} → (m : List A) →  m >>= return ≡ m
right-id-law [] = refl
right-id-law (x ∷ m) rewrite foldl-unf (x ∷ []) m return = cong (_∷_ x) (right-id-law m) 


-- associativity
assoc : {A B C : Set}  → (m : List A) → (f : A → List B)
  → (g : B → List C)
  → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
assoc [] f g = refl
assoc (x ∷ m) f g rewrite foldl-unf (f x) m f
 | foldl-unf ((f x) >>= g) m (λ x → f x >>= g)  
 | >>=split (f x) (m >>= f) g  
 | assoc m f g = refl 

{- some additional laws -}
>>=cong  : ∀ {X Y : Set} → (f g : X → List Y) → (xs : List X) → (∀ x → f x ≡ g x) → xs >>= f ≡ xs >>= g
>>=cong f g [] p = refl
>>=cong f g (x ∷ xs) p 
 rewrite >>=split [ x ] xs f
 | >>=split [ x ] xs g
 | p x 
 | >>=cong f g xs p = refl

list-monad-ht : {X Y : Set}(e : Y)(xs : List X)(f : X → List Y) → (x : X)  
 → x ∈ xs
 → e ∈ f x 
 → e ∈ (xs >>= f)
list-monad-ht e [] f x () ein
list-monad-ht e (x ∷ xs) f .x here ein 
 rewrite >>=split [ x ] xs f = ∈-weak-rgt ein
list-monad-ht e (x ∷ xs) f x₁ (there xin) ein 
 rewrite >>=split [ x ] xs f 
 = ∈-weak-lft {_} {f x} (list-monad-ht e xs f x₁ xin ein)


list-monad-th : {X Y : Set}(e : Y)(xs : List X)(f : X → List Y) 
 →  e ∈ (xs >>= f) →  Σ[ x ∈ X ] x ∈ xs × e ∈ f x
list-monad-th e [] f ()
list-monad-th e (x ∷ xs) f ein 
 rewrite >>=split [ x ] xs f with ∈-split {_} {f x} {xs >>= f} ein
list-monad-th e (x ∷ xs) f ein | inj₁ x₁ = x , here , x₁
list-monad-th e (x ∷ xs) f ein | inj₂ y with list-monad-th e xs f y 
... | (p1 , p2 , p3) = p1 , there p2 , p3
