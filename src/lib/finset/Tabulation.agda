


module Tabulation where

open import Data.Bool hiding (_≟_)
open import Data.Sum  hiding (map)
open import Data.Product  hiding (map)
open import Data.Maybe hiding (map ; All)
open import Data.List
open import Data.Empty

open import Relation.Binary.PropositionalEquality
   hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Utilities.BoolProperties
open import Utilities.ListProperties hiding (end)
open import Utilities.ListsAddition
open import Utilities.Logic

open import FiniteSubset hiding (fromList)
open import Finiteness 


fromListPartial : {X Y : Set} → DecEq X 
  → (xys : List (X × Y)) → NoDup (map proj₁ xys) 
  → X → Maybe Y
fromListPartial eq xys nodup x with eq2in eq x (map proj₁ xys) 
fromListPartial eq xys nodup x | yes x₁ with map∃ eq x proj₁ xys x₁ 
... | o1 , o2 , o3 = just (proj₂ o1)
fromListPartial eq xys nodup x | no y = nothing


fromListPartialSound : {X Y : Set} → (d : DecEq X) 
  → (xs : List (X × Y)) → (nodup : NoDup (map proj₁ xs))
  → ∀ x y → (x , y) ∈ xs
  → fromListPartial d xs nodup x ≡ just y
fromListPartialSound d xs nd x y xyin with eq2in d x (map proj₁ xs) 
fromListPartialSound d xs nd x y xyin | yes x₁ with map∃ d  x proj₁ xs x₁ 
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl with nd x x₁
... | q1 , q2 , q3 , q4 , q5 with ∃-after-map (x , y') xs proj₂ z2 
    | ∃-after-map (x , y) xs proj₂ xyin
... | b | v  with ∃-split (x , y) xs xyin 
... | o1 , o2 , o3 rewrite o3 with ∈-split {_} {o1} {((x , y) ∷ o2)} z2 
... | inj₁ k with notNoDup {_} {d} 
                     (map (λ r → proj₁ r) (o1 ++ (x , y) ∷ o2)) 
                     (map proj₁ o1 , map proj₁ ((x , y) ∷ o2) , x , 
                        maphom o1 ((x , y) ∷ o2) proj₁ , 
                          ∃-after-map (x , y') o1 proj₁ k , here) nd 
... | ()
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , .y) , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ here = refl
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k) 
  rewrite ++-assoc o1 ((x , y) ∷ []) o2 with ∈-split {_} {(o1 ++ (x , y) ∷ [])} {o2} z2
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k) | inj₁ xyin1 
  with ∈-split {_} {o1} {(x , y) ∷ []}  xyin1 
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k) | inj₁ xyin1  
  | inj₁ o with notNoDup {_} {d} (map (λ r → proj₁ r) ((o1 ++ (x , y) ∷ []) ++ o2)) 
     (map proj₁ (o1 ++ (x , y) ∷ []) , 
       map proj₁ o2 , x , maphom (o1 ++ (x , y) ∷ []) o2 proj₁ , 
         ∈-eq-cong x (map proj₁ o1 ++ x ∷ []) (map (λ r → proj₁ r) (o1 ++ (x , y) ∷ [])) 
          (∈-weak-lft {_} {map proj₁ o1} {x ∷ []} {x} here) 
             (sym (maphom o1 ((x , y) ∷ [])  proj₁))  , 
               ∃-after-map (x , y') o2 proj₁ k ) nd
... | ()
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , .y) , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k) 
  | inj₁ xyin1  | inj₂ here = refl
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 
  | inj₂ (there k) | inj₁ xyin1  | inj₂ (there ()) 
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k)  
  | inj₂ xyin1 with ∃-after-map (x , y') o2 proj₁ xyin1 
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v | o1 , o2 , o3 | inj₂ (there k)  
  | inj₂ xyin1 | inp with notNoDup {_} {d} 
     (map (λ r → proj₁ r) ((o1 ++ (x , y) ∷ []) ++ o2)) 
       (map proj₁ (o1 ++ (x , y) ∷ []) , map (λ r → proj₁ r) o2 , x , 
         maphom (o1 ++ (x , y) ∷ []) o2 proj₁ , ∈-eq-cong x (map proj₁ o1 ++ x ∷ []) 
          (map (λ r → proj₁ r) (o1 ++ (x , y) ∷ [])) 
            (∈-weak-lft {_} {map proj₁ o1} {x ∷ []} {x} here) 
              (sym (maphom o1 ((x , y) ∷ [])  proj₁)) , inp) nd
fromListPartialSound d xs nd x y xyin | yes x₁ | (.x , y') , z2 , refl 
  | q1 , q2 , q3 , q4 , q5 | b | v 
  | o1 , o2 , o3 | inj₂ (there k)  | inj₂ xyin1 | inp | () 
fromListPartialSound d xs nd x y₁ xyin | no y 
  with y (∃-after-map (x , y₁) xs proj₁ xyin)
... | ()

                

fromList : {X Y : Set} → (kf : ListableNoDup X) 
  → (xs : List (X × Y))
  → (proj₁ kf) SubSetOf (map proj₁ xs) 
  → NoDup (map proj₁ xs) 
  → X → Y
fromList (els , elsC , nd) xs sub nodup el 
  with inspect (fromListPartial (lstblEq (els , elsC)) xs nodup el)
fromList (els , elsC , nd) xs sub nodup el | it (just y) z = y
fromList (els , elsC , nd) xs sub nodup el | it nothing z with sub {el} (elsC el)
fromList (els , elsC , nd) xs sub nodup el | it nothing z 
  | o with   map∃ (lstblEq (els , elsC)) el proj₁ xs o
fromList (els , elsC , nd) xs sub nodup .el | it nothing z 
  | o | (el , proj₂) , mp2 , refl 
  rewrite fromListPartialSound (lstblEq (els , elsC)) 
  xs nodup el proj₂ mp2 with z
... | ()



fromListSound : {X Y : Set} → (kf : ListableNoDup X) 
  → (xs : List (X × Y))
  → (sb : (proj₁ kf) SubSetOf (map proj₁ xs))
  → (nd : NoDup (map proj₁ xs))
  → ∀ x y → (x , y) ∈ xs
  → fromList kf xs sb nd x ≡ y
fromListSound (els , elsComp , nd) xs sub nodup el y pin 
  with inspect (fromListPartial (lstblEq (els , elsComp)) xs nodup el)
fromListSound (els , elsComp , nd) xs sub nodup el y pin | it (just y') x₁ 
  = cong (maybe (λ x → x) y') (trans (sym x₁) 
  (fromListPartialSound (lstblEq (els , elsComp)) xs nodup el y pin))
fromListSound (els , elsComp , nd) xs sub nodup el y pin | it nothing z 
  with map∃ (lstblEq (els , elsComp)) el proj₁ xs (sub {el} (elsComp el))
fromListSound (els , elsComp , nd) xs sub nodup el y pin | it nothing z 
  | (.el , proj₂) , p2 , refl with trans (sym z) 
  (fromListPartialSound (lstblEq (els , elsComp)) xs nodup el y pin)
... | ()


fromListComplete : {X Y : Set} → (kf : ListableNoDup X) 
  → (xs : List (X × Y))
  → (sb : (proj₁ kf) SubSetOf (map proj₁ xs))
  → (nd : NoDup (map proj₁ xs))
  → ∀ x y → fromList kf xs sb nd x ≡ y
  → (x , y) ∈ xs
fromListComplete (els , elsC , nd') xs sb nd e y frpr with sb (elsC e) 
... | o with map∃  (lstblEq (els , elsC)) e proj₁  xs o 
fromListComplete (els , elsC , nd') xs sb nd e y frpr | o 
  | (.e , y') , pr2 , refl 
  rewrite trans (sym frpr) 
                (fromListSound (els , elsC , nd') xs sb nd e y' pr2) 
  = pr2


toList : {X Y : Set} → List X → (X → Y) → List (X × Y)
toList xs f = map (λ x → (x , f x)) xs


toListComplete : {X Y : Set} → (f : X → Y) 
  → (xs : List X)
  → ∀ x y → x ∈ xs → f x ≡ y
  → (x , y) ∈ toList xs f
toListComplete f xs x y xin fx with ∃-split x xs xin
... | o1 , o2 , o3  rewrite o3 
  | maphom o1 (x ∷ o2) (λ x₁ → x₁ , f x₁) 
  | fx = ∈-weak-lft {_} {(map (λ x₁ → x₁ , f x₁) o1)} 
         {(x , y) ∷ map (λ x₁ → x₁ , f x₁) o2} here


toListSoundHelp : {X Y : Set} → (f : X → Y) 
  → (xs : List X)  
  → ∀ x y → (x , y) ∈ toList xs f
  → x ∈ xs
toListSoundHelp f [] x y ()
toListSoundHelp f (x ∷ xs) .x .(f x) here 
  = here
toListSoundHelp f (x ∷ xs) x₁ y (there xyin) 
  = there (toListSoundHelp f xs x₁ y xyin)


toListSound : {X Y : Set} → (f : X → Y) 
  → (xs : List X) → NoDup xs 
  → ∀ x y → (x , y) ∈ toList xs f
  → f x ≡ y
toListSound f xs nd x y xyin with nd x (toListSoundHelp f xs x y xyin)
... | o1 , o2 , o3 , o4 , o5  rewrite o3 | maphom o1 (x ∷ o2) (λ x₁ → x₁ , f x₁)  
 with ∈-split {_} {map (λ x₁ → x₁ , f x₁) o1} 
      {(x , f x) ∷ map (λ x₁ → x₁ , f x₁) o2} xyin
... | inj₁ z with map-cong proj₁ (x , y) (map (λ x₁ → x₁ , f x₁) o1) z 
... | xin rewrite map-pr1 o1 f = ex-falso-quodlibet (o4 xin)
toListSound f xs nd x .(f x) xyin | o1 , o2 , o3 , o4 , o5  
  | inj₂ here = refl
toListSound f xs nd x y xyin | o1 , o2 , o3 , o4 , o5 | inj₂ (there z) 
  with map-cong proj₁ (x , y) (map (λ x₁ → x₁ , f x₁) o2) z 
... | xin rewrite map-pr1 o2 f = ex-falso-quodlibet (o5 xin)


Tbl : Set → Set → Set
Tbl X Y = Σ[ xs ∈ List (X × Y) ] 
          Σ[ kf ∈ ListableNoDup X ]
          All (map proj₁ xs) ×
          NoDupInd (map proj₁ xs)



toTbl : {X Y : Set} → ListableNoDup X → (X → Y) → Tbl X Y
toTbl (f1 , f2 , f3) f = toList f1 f , (f1 , f2 , f3) , sub , nod
 where
  sub : All (map proj₁ (toList f1 f))   
  sub rewrite map-pr1 f1 f = f2 

  nod : NoDupInd (map (λ r → proj₁ r) (toList f1 f))
  nod rewrite map-pr1 f1 f = f3



fromTbl : {X Y : Set} → Tbl X Y → X → Y
fromTbl (ls , f , p1 , p2) x = fromList f ls (λ x → p1 _) (NoDupInd-corr _ p2) x


  
allCheck : {X : Set}
     → Listable X 
     → (xs : List X)
     → Dec (All xs)
allCheck lstbl xs with subset-dec (lstblEq lstbl) (proj₁ lstbl) xs
... | yes p = yes (λ x → p ((proj₂ lstbl) _))
... | no  p = no (λ pp → p (λ z → pp _))

ndCheck : {X : Set} 
     → Listable X 
     → (xs : List X)
     → Dec (NoDupInd xs)
ndCheck lstbl = nodupDec2 (lstblEq lstbl)


createTbl : {X Y : Set} → (xs : List (X × Y)) 
  → (lstbl : Listable X)
  → {a : ∥ allCheck lstbl (map proj₁ xs) ∥}
  → {n : ∥ ndCheck  lstbl (map proj₁ xs) ∥}
  → Tbl X Y
createTbl xs lstbl {a} {n} 
  = xs , lstbl2nodup lstbl , ∥-∥-yes _ {a} , ∥-∥-yes _ {n}


tofrom : {X Y : Set} → (f : ListableNoDup X) → (t : Tbl X Y) 
  → (proj₁ t) SubSetOf (proj₁ (toTbl f (fromTbl t)))
tofrom (f1 , f2 , f3) (ls , f , p1 , p2) x 
 = toListComplete _ _ _ _ (f2 _) (fromListSound f ls (λ z → p1 _) (NoDupInd-corr _ p2) _ _ x)



fromto : {X Y : Set} → (f : ListableNoDup X) → (fn : X → Y) 
  → ∀ x → fromTbl (toTbl f fn) x ≡ fn x
fromto (proj₁ , proj₂ , proj₃) fn x 
  with toListComplete fn proj₁ x (fn x) (proj₂ _) refl
... | o = fromListSound 
  (proj₁ , proj₂ , proj₃) 
  (map (λ x₁ → x₁ , fn x₁) proj₁) _ _ 
  x (fn x) o



fromPure : {X Y : Set}{eq : DecEq X}{b : Bool} 
 → (f : FiniteSubSet X eq b) 
 → (X → Y) 
 → Element f → Y
fromPure  f fun (proj₁ , proj₂) = fun proj₁


_↦_ : {X Y : Set}{eq : DecEq X} 
  →  {b : Bool} → {f : FiniteSubSet X eq b}
  → (c : X)
  → {cp : ∥ eq2in eq c (listOf f) ∥ }
  → Y → (Element f × Y)
_↦_ c {cp = cp} y  = (c , cp) , y 
