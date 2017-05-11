
module Combinators where


open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Data.List hiding (product ; sum ; [_])
open import Data.Empty
open import Data.Unit hiding (_≟_ ; _≤_)
open import Data.Sum hiding (map ; [_,_])
open import Data.Product hiding (map ; <_,_>)
open import Data.Bool

open import Utilities.ListMonad
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic


open import Finiteness 



union : {X : Set} → {P Q : X → Set} 
  → ListableSubset X P 
  → ListableSubset X Q 
  → ListableSubset X (λ x → P x ⊎ Q x)
union {X} {P} {Q} (els1 , p2i1 , i2p1) (els2 , p2i2 , i2p2) 
  = els1 ++ els2 , i2p' , p2i'
  where
    ∈-split' : {X : Set} → {x : X} → (xs₁ xs₂ : List X) 
         →  x ∈ (xs₁ ++ xs₂)  → (x ∈ xs₁) ⊎ (x ∈ xs₂)
    ∈-split' xs₁ xs₂ = ∈-split {_} {xs₁} {xs₂}

    p2i' : (x : X) → P x ⊎ Q x → x ∈ (els1 ++ els2)
    p2i' x (inj₁ x₁) = ∈-weak-rgt {_} {els2} (i2p1 x x₁)
    p2i' x (inj₂ y) = ∈-weak-lft {_} {els1} (i2p2 x y)

    i2p' : (x : X) → x ∈ (els1 ++ els2) → P x ⊎ Q x
    i2p' x xin with ∈-split' els1 els2 xin  
    i2p' x xin | inj₁ x₁ = inj₁ (p2i1 x x₁)
    i2p' x xin | inj₂ y = inj₂ (p2i2 x y)



open import Relation.Nullary.Decidable 

rest : {X : Set} → (x : X) → (P : X → Set) → (pd : Dec (P x)) 
   → ⌊ pd ⌋ ≡ true  → P x
rest x p (yes p₁) pr = p₁
rest x p (no ¬p) ()

restOp : {X : Set} → (x : X) → (P : X → Set) → (pd : Dec (P x)) 
   → P x → ⌊ pd ⌋ ≡ true
restOp x p (yes p₁) px = refl
restOp x p (no ¬p) px = ex-falso-quodlibet (¬p px)

intersection : {X : Set} → {P Q : X → Set} 
  → (Pdec : (x : X) → Dec (P x))
  → ListableSubset X P 
  → ListableSubset X Q 
  → ListableSubset X (λ x → P x × Q x)
intersection {X} {P} {Q} pd (els1 , p2i1 , i2p1) 
  (els2 , p2i2 , i2p2) 
    = filter (λ x → ⌊ pd x ⌋) els2 , i2p' , p2i'

   where
    
    p2i' : (x : X) → P x × Q x → x ∈ filter (λ x₁ → ⌊ pd x₁ ⌋) els2
    p2i' x (px , qx)  = filter-in2 els2 x (λ x₁ → ⌊ pd x₁ ⌋) (i2p2 x qx) (restOp x P (pd x) px)
    
    i2p' : (x : X) → x ∈ filter (λ x₁ → ⌊ pd x₁ ⌋) els2 → P x × Q x
    i2p' x xin = p2i1 x (i2p1 x (rest x P (pd x) ((filter-el x els2 (λ x₁ → ⌊ pd x₁ ⌋) xin)))) , 
              p2i2 x (filter-∈ x els2 (λ x₁ → ⌊ pd x₁ ⌋) xin)




<_,_> : {X Y : Set} → (X → Set) → (Y → Set) → (X × Y → Set)
<_,_> P Q (x , y) = P x × Q y



[_,,_] : {X Y : Set} → (X → Set) → (Y → Set) → (X ⊎ Y → Set)
[_,,_] P Q (inj₁ x) = P x
[_,,_] P Q (inj₂ y) = Q y



product : {X : Set}{P : X → Set}{Y : Set}{Q : Y → Set}
  → ListableSubset X P 
  → ListableSubset Y Q 
  → ListableSubset (X × Y) < P , Q > 
product {X} {P} {Y} {Q} (els1 , p2i1 , i2p1) 
  (els2 , p2i2 , i2p2) = 
  els1 >>= (λ x → 
  els2 >>= (λ y → 
  return (x , y))) , hlp , hlp2

    where
     hlp2 : (x : X × Y) → < P , Q > x →
        x ∈ els1 >>= (λ x₁ → els2 >>= (λ y → return (x₁ , y)))
     hlp2 (x1 , y1) (pr1 , pr2)  = list-monad-ht (x1 , y1) els1 
       (λ x₁ → els2 >>= (λ y → return (x₁ , y)))  x1  
       (i2p1 x1  pr1) 
       (list-monad-ht (x1 , y1) els2 _ y1 (i2p2 y1  pr2)  here)
 
     hlp : (x : X × Y) →
      x ∈ els1 >>= (λ x₁ → els2 >>= (λ y → return (x₁ , y))) →
      < P , Q > x 
     hlp x pr with list-monad-th x els1 (λ x₁ → els2 >>= (λ y → return (x₁ , y))) pr 
     ... | o1 , o2 , o3 with list-monad-th x els2 _ o3 
     hlp .(o1 , p1) pr | o1 , o2 , o3 | p1 , p2 , here = p2i1  o1 o2 , p2i2 p1 p2
     hlp x pr | o1 , o2 , o3 | p1 , p2 , there ()





sum : {X : Set}{P : X → Set}{Y : Set}{Q : Y → Set}
  → ListableSubset X P 
  → ListableSubset Y Q 
  → ListableSubset (X ⊎ Y) [ P ,, Q ]
sum {X} {P} {Y} {Q} (els1 , p2i1 , i2p1) (els2 , p2i2 , i2p2) 
  = Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2 , hlp , hlp2
    where
      hlp : (x : X ⊎ Y) → x ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2) → [ P ,, Q ] x
      hlp (inj₁ x) xi = p2i1 x (xi1' x els1 els2 xi) 
        where
          xi1'   : {X : Set} → (x : X) → (els1 : List X) 
                    → {Y : Set} →  (els2 : List Y)  
                   → inj₁ x ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2)
                   → x ∈ els1
          xi1' x [] [] ()
          xi1' x [] (x₁ ∷ ys) (there pr) = xi1' x [] ys pr
          xi1' x₁ (.x₁ ∷ els1) ys here = here
          xi1' x (x₁ ∷ els1) ys (there pr) = there (xi1' x els1 ys pr)
      hlp (inj₂ y) xi = p2i2 y (xi2' y els1 els2 xi)
        where
          xi2'   : {X : Set}{Y : Set} → (y : Y) → (els1 : List X) 
                   →  (els2 : List Y)  
                   → inj₂ y ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2)
                   → y ∈ els2
          xi2' y [] [] ()
          xi2' y [] (.y ∷ els2) here = here
          xi2' y [] (x ∷ els2) (there pr) = there (xi2' y [] els2 pr)
          xi2' y (x ∷ els1) els2 (there pr) = xi2' y els1 els2 pr


      hlp2 : (x : X ⊎ Y) → [ P ,, Q ] x →
        x ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2)
      hlp2 (inj₁ x) pr = xi1 x els1 els2 (i2p1  x pr)
        where
          xi1   : {X : Set} → (x : X) → (els1 : List X) 
                    → {Y : Set} →  (els2 : List Y)  → x ∈ els1
                  → inj₁ x ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2)
          xi1 x ._ els2 here = here
          xi1 x ._ els2 (there xi) = there (xi1 x _ els2 xi)
      hlp2 (inj₂ y) pr = xi2 y  els1 els2 (i2p2 y pr)
        where
          xi2   : {X Y : Set} → (y : Y) → (els1 : List X) 
                    →  (els2 : List Y)  → y ∈ els2
                  → inj₂ y ∈ (Data.List.map inj₁ els1 ++ Data.List.map inj₂ els2)
          xi2 y [] [] ()
          xi2 y [] (.y ∷ els2) here = here
          xi2 y [] (x ∷ els2) (there pr) = there (xi2 y [] els2 pr)
          xi2 y (x ∷ els1) els2 pr = there (xi2 y els1 els2 pr)



kfWithEq2Dec : {X : Set}{P : X → Set}
  → DecEq X
  → ListableSubset X P
  → ∀ x → Dec (P x)
kfWithEq2Dec d (l , s , c) x with eq2in d x l 
kfWithEq2Dec d (l , s , c) x | yes p = yes (s _ p)
kfWithEq2Dec d (l , s , c) x | no ¬p = no (λ px → ¬p (c _ px))
