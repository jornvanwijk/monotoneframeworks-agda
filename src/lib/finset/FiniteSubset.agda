

module FiniteSubset where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Data.Product hiding (map)
open import Data.List
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.Bool

open import Function

open import Utilities.Logic 
open import Utilities.ListProperties
open import Utilities.NatProperties



open import Finiteness


data FiniteSubSet (X : Set) (eq : DecEq X) : Bool → Set where 
  fs-plain  : List X → FiniteSubSet X eq true
  fs-nojunk : (els : List X) → {nd :  ∥ nodupDec eq els ∥} 
    → FiniteSubSet X eq false


FSS : Set₁
FSS = Σ[ X ∈ Set ] Σ[ eq ∈ DecEq X ] Σ[ b ∈ Bool ] FiniteSubSet X eq b


listOf : {X : Set}{eq : DecEq X}{b : Bool} → FiniteSubSet X eq b → List X
listOf (fs-plain x) = x
listOf (fs-nojunk els) = els

open import Utilities.ListsAddition

fromList : {X : Set}{eq : DecEq X} → List X → (b : Bool) → FiniteSubSet X eq b
fromList xs true = fs-plain xs
fromList {eq = eq} xs false = fs-nojunk (remDup (eq2in eq) xs) 
   {∥-∥-prop2 (remDupCorrect  (eq2in eq) xs) _}


Element : {X : Set}{eq : DecEq X}{b : Bool} → FiniteSubSet X eq b → Set
Element {X} {eq} f = Σ[ x ∈ X ] ∥ eq2in eq x (listOf f) ∥


-- this equality is more efficient, than the one you can get from fsListable
fsEq : {C : Set}{eq : DecEq C}{b : Bool} 
  → (se : FiniteSubSet C eq b) → DecEq (Element se)
fsEq {eq = eq} se (e1 , e2) (e3 , e4) with eq e1 e3 
fsEq {eq = eq} se (e1 , e2) (.e1 , e4) | yes refl 
  rewrite ∥-∥-prop (eq2in eq e1 (listOf se)) e2 e4 = yes refl
fsEq {eq = eq} se (e1 , e2) (e3 , e4) | no ¬p 
  = no (λ p → ¬p (cong proj₁ p))


fsListable : {X : Set} → {eq : DecEq X} → {b : Bool} → (fs : FiniteSubSet X eq b) 
  → Listable (Element fs)
fsListable {eq = eq} fs = let x = listOf fs in 
     map-in x (λ { (p1 , p2) → p1 ,  ∥-∥-prop2 p2 (eq2in eq p1 x) } ) , hlp
  where
   hlp : All (map-in (listOf fs) (λ { (p1 , p2) → p1 ,  
          ∥-∥-prop2 p2 (eq2in eq p1 (listOf fs)) } ))
   hlp (xe , pe) with map-in-pr (listOf fs) 
        (λ { (p1 , p2) → p1 ,  ∥-∥-prop2 p2 (eq2in eq p1 (listOf fs)) } ) xe (∥-∥-prop3 _ pe) 
   ... | o1 , o2 rewrite ∥-∥-prop _ pe (∥-∥-prop2 o1 (eq2in eq xe (listOf fs))) = o2


elementsOf : {X : Set} → {eq : DecEq X} → {b : Bool} → (fs : FiniteSubSet X eq b) 
  → List (Element fs)
elementsOf fs = proj₁ $ fsListable fs


elementsOfComplete : {X : Set} → {eq : DecEq X} → {b : Bool} → (fs : FiniteSubSet X eq b)
  → (e : Element fs) → e ∈ elementsOf fs
elementsOfComplete fs e = proj₂ (fsListable fs) e


ndlft : {X : Set} → (xs : List X) → NoDupInd xs → NoDupInd (lft xs)
ndlft .[] end = end
ndlft {X} (x ∷ xs) (x₁ ::: nd) = hlp1 ::: nd2' _ (lft _) hlp2 (ndlft _ nd)
  where

   ∈b : ∀{a} → {X : Set a} → (y1 y2 : X) → (ys : List X) → (p1 p2 : y1 ∈ ys) 
      → (_,_ {a} {a} {X} {λ x → x ∈ (y2 ∷ ys)} y1 ((there {a} {X} {y1} {y2} {ys} p1))) ≡ 
      ((y1 , there {a} {X} {y1} {y2}  {ys} p2)) → p1 ≡ p2
   ∈b y1 y ys p1 .p1 refl = refl
   
   hlp2 : (y1 y2 : Σ[ x ∈ X ] x ∈ xs) →
      (proj₁ y1 , there (proj₂ y1)) ≡ (proj₁ y2 , there (proj₂ y2)) →
      y1 ≡ y2
   hlp2 (y1 , pr1) (y2 , pr2) pr with cong proj₁ pr 
   hlp2 (y1 , pr1) (y2 , pr2) pr | o rewrite o | ∈b y2  _  _  pr1 pr2 pr = refl

   hlp1 : ¬
      (x , here ) ∈ map (λ ep → proj₁ ep , there (proj₂ ep)) (lft xs)
   hlp1 pr with map∃' (x , here) _  (lft xs) pr 
   hlp1 pr | o1 , o2 , ()


mapnod : {X Y : Set} → (els : List X) 
 → (f : Σ[ e ∈ X ] e ∈ els → Y)
 → (∀ x1 x2 → f x1 ≡ f x2 → x1 ≡ x2)
 → NoDupInd els
 → NoDupInd (map-in els f)
mapnod xs f ft nd = nd2' f (lft xs) ft (ndlft xs nd) 


elementsOfNoDup : {X : Set} → {eq : DecEq X} → {b : Bool} → (fs : FiniteSubSet X eq false) 
  → NoDupInd (elementsOf fs)
elementsOfNoDup {X} {eq} (fs-nojunk els {nd}) with NoDupInd-corr2 _ (∥-∥-prop3 _ nd) 
... | o = mapnod els (λ { (p1 , p2) → p1 ,  ∥-∥-prop2 p2 (eq2in eq p1 els) } ) z o
   where
     z : (x1 x2 : Σ X (λ e → e ∈ els)) →
      (proj₁ x1 , ∥-∥-prop2 (proj₂ x1) (eq2in eq (proj₁ x1) els)) ≡
      (proj₁ x2 , ∥-∥-prop2 (proj₂ x2) (eq2in eq (proj₁ x2) els)) →
      x1 ≡ x2
     z (e1 , e1p) (e2 , e2p) pr with cong proj₁ pr 
     z (e1 , e1p) (.e1 , e2p) pr | refl 
       rewrite NoDupInd-pr e1 els e1p e2p o = refl




-- monad 
open import Utilities.ListMonad renaming (return to returnm)

return : {X : Set}{eq : DecEq X}{b : Bool} → X → FiniteSubSet X eq b
return {b = true} x = fs-plain (x ∷ []) 
return {b = false} x = fs-nojunk (x ∷ []) {tt}


bind : {X Y : Set}{eqx : DecEq X}{eqy : DecEq Y}{b1 b2 : Bool}
  → FiniteSubSet X eqx b1
  → (X → FiniteSubSet Y eqy b2 )
  → (b : Bool)
  → FiniteSubSet Y eqy b
bind f c = fromList $ (listOf f) >>= (λ x → listOf $ c x)


mzero : {X : Set}{eq : DecEq X}{b : Bool} → FiniteSubSet X eq b
mzero {b = false} = fs-nojunk []
mzero {b = true} = fs-plain []

if_then_ : {X : Set}{eq : DecEq X}{b : Bool}
  → Bool → FiniteSubSet X eq b
  → FiniteSubSet X eq b
if b then c = if b then c else mzero

syntax bind A (λ x → B) b = for x ∈ A as b do B

open import Relation.Nullary.Decidable
open import Function


_∩_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq (b1 ∧ b2)
_∩_ {C} {eq = _==_} {b1} {b2}  X Y = 
   for x ∈ X as _ do 
     for y ∈ Y as true do 
        if ⌊ x == y ⌋ then return {b = true} x 

_∪_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
  → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
  → FiniteSubSet C eq (b1 ∧ b2)
_∪_ {C} {eq = _==_} {b1} {b2}  X Y = fromList (listOf X ++ listOf Y) _







