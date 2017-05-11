
module Utilities.ListsAddition where

open import Data.List hiding (filter)
open import Data.Bool hiding (_∨_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utilities.Logic

open import Utilities.ListProperties

open import Data.Empty
infix 5 _∉_
_∉_ : {X : Set} → X → List X → Set
_∉_ x xs = x ∈ xs → ⊥

data SubSeq {X : Set} (F : X → Bool) :  List X → List X → Set where
  con1 : SubSeq F [] []
  con2 : ∀ {xs ys y} → SubSeq F xs ys → F y ≡ true → SubSeq F xs (y ∷ ys)
  con3  : ∀ {xs ys y} → SubSeq F xs ys → SubSeq F (y ∷ xs) (y ∷ ys)


combs : {X : Set} → (f : X → Bool) → List X → List (List X)
combs f xs 
  = foldr (λ x res → if f x then res ++ (map (_∷_ x) res) else map (_∷_ x) res) [ [] ] xs


open import Data.Sum


remEl : {L : Set} → ((x y : L) → x ≡ y ⊎  x ≢ y)  →  List L → L → List L
remEl dec [] e = []
remEl dec (x ∷ xs) e with dec x e  
remEl dec (x ∷ xs) e | inj₁ x₁ = remEl dec xs e
remEl dec (x ∷ xs) e | inj₂ y = x ∷ (remEl dec xs e)


diff : {L : Set} → ((x y : L) → x ≡ y ⊎  x ≢ y) → List L → List L → List L
diff dec xs [] = xs
diff dec xs (y ∷ ys) = diff dec (remEl dec xs y)  ys


remDup2 : {X : Set} → DecIn X → List X → List X
remDup2 ∈? xs = foldl (λ res e → if dec2bool (∈? e res) 
                                  then res else e ∷ res) [] xs

remDup : {X : Set} → DecIn X → List X → List X
remDup ∈? xs = foldr (λ e res → if dec2bool (∈? e res) 
                                  then res else e ∷ res) [] xs

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary
open import Data.Product

remDupSound : {X : Set} → (∈? : DecIn X) → (x : X)    → (xs : List X) → x ∈ xs → x ∈ remDup ∈? xs
remDupSound ∈? x [] ()
remDupSound ∈? x (.x ∷ xs) here with ∈? x (remDup ∈? xs)
remDupSound ∈? x (.x ∷ xs) here | yes p = p
remDupSound ∈? x (.x ∷ xs) here | no ¬p = here
remDupSound ∈? x (x₁ ∷ xs) (there xin) with remDupSound ∈? x xs xin
... | o with ∈? x₁ (remDup ∈? xs)
remDupSound ∈? x (x₁ ∷ xs) (there xin) | o | yes p = o
remDupSound ∈? x (x₁ ∷ xs) (there xin) | o | no ¬p = there o


remDupComplete : {X : Set} → (∈? : DecIn X) → (x : X) → (xs : List X) → x ∈ (remDup ∈? xs) → x ∈ xs
remDupComplete ∈? x [] ()
remDupComplete ∈? x (x₁ ∷ xs) xin with ∈? x₁ (remDup ∈? xs) 
remDupComplete ∈? x (x₁ ∷ xs) xin | yes p = there (remDupComplete ∈? x xs xin)
remDupComplete ∈? x₁ (.x₁ ∷ xs) here | no ¬p = here
remDupComplete ∈? x (x₁ ∷ xs) (there xin) | no ¬p = there (remDupComplete ∈? x xs xin)


remDupCorrect : {X : Set} → (∈? : DecIn X) → (xs : List X) → NoDup (remDup ∈? xs)
remDupCorrect ∈? [] x ()
remDupCorrect ∈? (x ∷ xs) x₁ x₂ with ∈? x (remDup ∈? xs)
remDupCorrect ∈? (x ∷ xs) x₁ x₂ | yes p with remDupCorrect ∈? xs x₁ x₂  
... | o1 , o2 , o3 , o4 , o5 = o1 , o2 , o3 , o4 , o5
remDupCorrect ∈? (x ∷ xs) .x here | no ¬p = [] , _ , refl , (λ { () }) , ¬p
remDupCorrect ∈? (x ∷ xs) x₁ (there x₂) | no ¬p with remDupCorrect ∈? xs x₁ x₂  | in2eq ∈? x₁ x 
remDupCorrect ∈? (x ∷ xs) .x (there x₂) | no ¬p | o1 , o2 , o3 , o4 , o5 
  | yes refl rewrite o3 
  = ex-falso-quodlibet (¬p (∈-weak-lft {_} {o1} {x ∷ o2} here))
remDupCorrect {X} ∈? (x ∷ xs) x₁ (there x₂) 
  | no ¬p₁ 
  | o1 , o2 , o3 , o4 , o5 
  | no ¬p 
  = x ∷ o1 , o2 , cong (_∷_ x) o3 , h x x₁ ¬p o4 , o5
  where
    h : (x x₁ : X) → ¬ x₁ ≡ x → ¬ x₁ ∈ o1  → ¬ x₁ ∈ (x ∷ o1)
    h x1 .x1 pr1 pr2 here = pr1 refl
    h x1 x₃  pr1 pr2 (there pr) = pr2 pr



{-
minprop : (xs ys : List (List L)) → (a : List L) → ((t : List L) → (t ∈ ys) → ¬ a SameEls t) → ((a ∷ xs) - ys) ≡ a ∷ (xs - ys)
minprop xs [] a prop = refl
minprop xs (ys ∷ ys₁) a prop with sameAsDec Leq a ys 
minprop xs (ys ∷ ys₁) a prop | inj₁ x = ex-falso-quodlibet (prop ys here x)
minprop xs (y ∷ ys) a prop | inj₂ i = minprop (xs -e y) ys a (λ t tin → prop t (there tin))


minprop2 : (xs ys : List (List L)) → (o : List L) → (a : List L) → o ∈ ys → a SameEls o  → ((a ∷ xs) - ys) ≡ (xs - ys)
minprop2 xs .(o ∷ xs₁) o a (here {.o} {xs₁}) sa with sameAsDec Leq a o 
minprop2 xs .(o ∷ xs₁) o a (here {.o} {xs₁}) sa | inj₁ x = refl
minprop2 xs .(o ∷ xs₁) o a (here {.o} {xs₁}) sa | inj₂ y = ex-falso-quodlibet (y sa)
minprop2 xs .(y ∷ xs₁) o a (there {.o} {y} {xs₁} oin) sa with sameAsDec Leq a y 
minprop2 xs .(y ∷ xs₁) o a (there {.o} {y} {xs₁} oin) sa | inj₁ x = refl
minprop2 xs .(y ∷ xs₁) o a (there {.o} {y} {xs₁} oin) sa | inj₂ y₁ = minprop2 (xs -e y) xs₁ o a  oin sa


minprop3' : (xs ys : List (List L))(zs : List L) →  (xs ++l ys) -e zs ≡ (xs -e zs) ++l (ys -e zs)
minprop3' [] ys zs = refl
minprop3' (xs ∷ xs₁) ys zs with sameAsDec Leq xs zs
minprop3' (xs ∷ xs₁) ys zs | inj₁ x = minprop3' xs₁ ys zs
minprop3' (xs ∷ xs₁) ys zs | inj₂ y = cong (_∷_ _) (minprop3' xs₁ ys zs)


minprop3 : (xs ys zs : List (List L)) →  (xs ++l ys) - zs ≡ (xs - zs) ++l (ys - zs)
minprop3 xs ys [] = refl
minprop3 xs ys (zs ∷ zs₁) rewrite minprop3' xs ys zs = minprop3 (xs -e zs) (ys -e zs) zs₁


minprop4 : (xs ys zs : List (List L)) → xs - (ys ++l zs) ≡ (xs - ys) - zs
minprop4 xs [] zs = refl
minprop4 xs (ys ∷ ys₁) zs = minprop4 (xs -e ys) ys₁ zs


len-min' : (xs : List (List L)) → (ys : List L) → length (xs -e ys) ≤ length xs
len-min' [] ys = ≤-t1 _
len-min' (xs ∷ xs₁) ys with sameAsDec Leq xs ys 
len-min' (xs ∷ xs₁) ys | inj₁ x = ≤-t2 _ _ (len-min' xs₁ ys)
len-min' (xs ∷ xs₁) ys | inj₂ y = s≤s (len-min' xs₁ ys)


len-min : (xs ys : List (List L)) → length (xs - ys) ≤ length xs
len-min xs [] = ≤-t1 _
len-min xs (ys ∷ ys₁) = ≤-t3 _ _ _ (len-min (xs -e ys) ys₁) (len-min' xs ys)

-}


{-
open import Data.Nat
eqℕ : ℕ → ℕ → Bool
eqℕ zero zero = true
eqℕ zero (suc b) = false
eqℕ (suc a) zero = false
eqℕ (suc a) (suc b) = eqℕ a b
ex₁ = combs (λ x → eqℕ x 2 ) (1 ∷ 2 ∷ 3 ∷ 2 ∷ [])
-}

{- fine -}
{-
filter : {X : Set} → (f : X → Bool) → List X → List X
filter f xs = foldl (λ res x → if f x then x ∷ res else res) [] xs
-}




{-filter′ f [] = []
filter′ f (x ∷ xs) with f x 
filter′ f (x ∷ xs) | true  = filter′ f xs
filter′ f (x ∷ xs) | false = x ∷ filter′ f xs
-}

{-
filterLem : {X : Set} → (xs : List X) → (f : X → Bool) → SubSeq f (filter′ f xs) xs
filterLem [] f = con1
filterLem (x ∷ xs) f with inspect' (f x)
filterLem (x ∷ xs) f | it true x₁ rewrite x₁ = con2 (filterLem xs f) x₁
filterLem (x ∷ xs) f | it false x₁ rewrite x₁ = con3 (filterLem xs f)


subseqLem : {X : Set}{f g : X → Bool}(xs ys : List X) → (∀ x → f x ≡ true → g x ≡ true) → SubSeq f xs ys → SubSeq g xs ys
subseqLem .[] .[] p con1 = con1
subseqLem xs .(y ∷ ys) p (con2 {.xs} {ys} {y} s x) = con2 (subseqLem xs ys p s) (p y x)
subseqLem .(y ∷ xs) .(y ∷ ys) p (con3 {xs} {ys} {y} s) = con3 (subseqLem xs  ys p s)
-}
