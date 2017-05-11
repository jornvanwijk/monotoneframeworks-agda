
module PredicateMatching where

open import Data.Bool hiding (_≟_)
open import Data.Sum  hiding (map)
open import Data.Product  hiding (map)
open import Data.Maybe hiding (map ; All)
open import Data.List

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Utilities.BoolProperties
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic

open import Finiteness


anySound : {X : Set} → (xs : List X) → (p : X → Bool) 
  → any p xs ≡ true → Σ[ x ∈ X ] x ∈ xs × p x ≡ true
anySound [] p ()
anySound (x ∷ xs) p pr with inspect (p x) 
anySound (x ∷ xs) p pr | it true x₁ rewrite x₁ = x , here , x₁
anySound (x ∷ xs) p pr | it false x₁ rewrite x₁ with anySound xs p pr 
... | z1 , z2 , z3 = z1 , there z2 , z3 


anyComplete : {X : Set} → (xs : List X) → (p : X → Bool) 
  → ∀ x → x ∈ xs →  p x ≡ true → any p xs ≡ true
anyComplete [] p x () px
anyComplete (x ∷ xs) p .x here px rewrite px = refl
anyComplete (x ∷ xs) p x₁ (there xin) px with p x 
anyComplete (x ∷ xs) p x₁ (there xin) px | true = refl
anyComplete (x ∷ xs) p x₁ (there xin) px | false = anyComplete xs p x₁ xin px


joinPreds : {X : Set} → List (X → Bool) → X → Bool
joinPreds [] x = false
joinPreds (x ∷ ls) x₁ = x x₁ ∨ joinPreds ls x₁


joinPredsSound : {X : Set} → (pd : List (X → Bool)) → ∀ z 
  → joinPreds pd z ≡ false 
  → ∀ p → p ∈ pd → p z ≡ false
joinPredsSound [] z pr p ()
joinPredsSound (x ∷ pd) z pr .x here with x z 
joinPredsSound (x ∷ pd) z () .x here | true
joinPredsSound (x ∷ pd) z pr .x here | false = refl
joinPredsSound (x ∷ pd) z pr x₁ (there pin) with x z 
joinPredsSound (x ∷ pd) z () x₁ (there pin) | true
joinPredsSound (x ∷ pd) z pr x₁ (there pin) | false 
  = joinPredsSound pd z pr x₁ pin  


joinPredsComplete : {X : Set} → ∀ x → (pd1 : List (X → Bool))
  → (∀ p' → p' ∈ pd1 → p' x ≡ false) 
  → joinPreds pd1 x ≡ false
joinPredsComplete x [] prop = refl
joinPredsComplete x (x₁ ∷ pd1) prop rewrite prop x₁ here 
  = joinPredsComplete x pd1 (λ p' p'in → prop p' (there p'in))


de-morgan : {X : Set} → (x : X → Bool) 
  → (pd1 : List (X → Bool)) → (xs : List X) 
  → filter (λ e → not (joinPreds pd1 e) ∧ not (x e)) xs ≡  
       filter (λ e → not ((x e) ∨ (joinPreds pd1 e))) xs
de-morgan x pd1 [] = refl
de-morgan x pd1 (x₁ ∷ xs) with x x₁ 
de-morgan x pd1 (x₁ ∷ xs) | true 
  rewrite ∧-comm (not (joinPreds pd1 x₁)) false = de-morgan x pd1 xs
de-morgan x pd1 (x₁ ∷ xs) | false 
  rewrite ∧-comm (not (joinPreds pd1 x₁)) true  
  with not (joinPreds pd1 x₁)
... | true = cong (_∷_ _) (de-morgan x pd1 xs)
... | false = (de-morgan x pd1 xs)



forallPredsSomeElement : {X : Set} → List (X → Bool) → List X → Bool
forallPredsSomeElement [] l2 = true
forallPredsSomeElement (x ∷ l1) l2 = any x l2 ∧ 
  forallPredsSomeElement l1 (filter (λ e → not (x e)) l2)


forallPredsSomeElementSplit : {X : Set} → (xs : List X) 
  → (pd1 pd2 : List (X → Bool))
  → forallPredsSomeElement (pd1 ++ pd2) xs ≡ 
       forallPredsSomeElement pd1 xs ∧ 
          forallPredsSomeElement pd2 (filter (λ e → not ((joinPreds pd1) e)) xs)
forallPredsSomeElementSplit xs [] pd2 rewrite filter-id xs = refl
forallPredsSomeElementSplit xs (x ∷ pd1) pd2 with any x xs 
forallPredsSomeElementSplit xs (x ∷ pd1) pd2 | false = refl
forallPredsSomeElementSplit xs (x ∷ pd1) pd2 | true 
  with forallPredsSomeElementSplit (filter (λ e → not (x e)) xs) pd1 pd2 
... | IH rewrite IH 
  with filter-nest xs 
         (λ x₁ → not (joinPreds pd1 x₁))
         (λ x₁ → not (x x₁))
... | nest rewrite nest with de-morgan x pd1 xs 
... | morg rewrite morg = refl


forallPredsSomeElementComplete : {X : Set} → (pd : List (X → Bool)) 
  → (xs : List X)
  → (p : X → Bool)
  → forallPredsSomeElement pd xs ≡ true
  → Σ[ x ∈ X ] x ∈ xs × p x ≡ true × 
     (∀ p' → p' ∈ pd → p' x ≡ false)
  → forallPredsSomeElement (pd ++ p ∷ []) xs ≡ true
forallPredsSomeElementComplete pd1 xs p pr (x , xin , px , prop) 
  rewrite forallPredsSomeElementSplit xs pd1 (p ∷ []) | pr 
  | anyComplete _ p x 
      (filter-in2 xs x (λ x₁ → not (joinPreds pd1 x₁)) xin 
      (not-inv2 _ (joinPredsComplete x pd1 prop))) px = refl


forallPredsSomeElementSound : {X : Set} → (pd1 pd2 : List (X → Bool)) 
  → (xs : List X)
  → (p : X → Bool)
  → forallPredsSomeElement (pd1 ++ p ∷ pd2) xs ≡ true
  → Σ[ x ∈ X ] x ∈ xs × p x ≡ true × (∀ p' → p' ∈ pd1 → p' x ≡ false) 
forallPredsSomeElementSound pd1 pd2 xs p pr 
  rewrite forallPredsSomeElementSplit xs pd1 (p ∷ pd2) 
  with forallPredsSomeElement pd1 xs 
forallPredsSomeElementSound pd1 pd2 xs p pr 
  | true  
  with inspect (any p (filter (λ e → not (joinPreds pd1 e)) xs)) 
forallPredsSomeElementSound pd1 pd2 xs p pr | true | it true q 
  rewrite q 
  with anySound (filter (λ e → not (joinPreds pd1 e)) xs) p q 
... | z1 , z2 , z3 = z1 , 
       filter-∈ z1 xs ((λ e → not (joinPreds pd1 e)))  z2 , z3 , 
       (λ p pin → joinPredsSound pd1 z1 
         (not-inv _ (filter-el z1 xs 
           (λ e → not (joinPreds pd1 e)) z2)) p pin)
forallPredsSomeElementSound pd1 pd2 xs p pr 
  | true 
  | it false q rewrite q with pr 
forallPredsSomeElementSound pd1 pd2 xs p pr 
  | true 
  | it false q | ()
forallPredsSomeElementSound pd1 pd2 xs p pr | false  with pr 
... | ()


unreached : {X : Set} → List (X → Bool) → List X → List (X → Bool)
unreached [] l2 = []
unreached (x ∷ l1) l2 = (if (any x l2) then [] else (x ∷ [])) ++ 
  unreached l1 (filter (λ e → not (x e)) l2)


unreachedSound' : {X : Set} → (ps : List (X → Bool)) → (xs : List X) 
  → unreached ps xs ≡ [] → forallPredsSomeElement ps xs ≡ true
unreachedSound' [] xs pr = refl
unreachedSound' (x ∷ ps) xs pr with any x xs 
unreachedSound' (x ∷ ps) xs pr | true = unreachedSound' ps _  pr
unreachedSound' (x ∷ ps) xs () | false



unreachedSound : {X : Set} 
  → (pd₁ pd₂ : List (X → Bool)) 
  → (xs : List X)
  → (p : X → Bool)
  → unreached (pd₁ ++ p ∷ pd₂) xs ≡ []
  → Σ[ x ∈ X ] x ∈ xs × p x ≡ true × 
     (∀ p' → p' ∈ pd₁ → p' x ≡ false) 
unreachedSound pd1 pd2 xs p unr 
  = forallPredsSomeElementSound pd1 pd2 xs p 
    (unreachedSound' (pd1 ++ p ∷ pd2) xs unr)


unreachedComplete' : {X : Set} → (ps : List (X → Bool)) → (xs : List X)
  → forallPredsSomeElement ps xs ≡ true → unreached ps xs ≡ []
unreachedComplete' [] xs pr = refl
unreachedComplete' (x ∷ ps) xs pr with any x xs 
unreachedComplete' (x ∷ ps) xs pr | true 
  = unreachedComplete' ps _ pr
unreachedComplete' (x ∷ ps) xs () | false


unreachedComplete : {X : Set} → (pd : List (X → Bool)) → (xs : List X)
  → unreached pd xs ≡ []
  → (p : X → Bool)
  → ∀ x
  → x ∈ xs  
  → p x ≡ true
  → (∀ p' → p' ∈ pd → p' x ≡ false)
  → unreached (pd ++ p ∷ []) xs ≡ []
unreachedComplete pd xs unr p x xin px pr 
  = unreachedComplete' (pd ++ p ∷ []) xs 
     (forallPredsSomeElementComplete pd xs p 
       (unreachedSound' pd  xs unr) (x , xin , px , pr))



isMatched : {X : Set} → X → List (X → Bool) → Bool
isMatched x xs = any (λ p → p x) xs


isMatchedSound : {X : Set} → (x : X) → (pds : List (X → Bool)) 
  → isMatched x pds ≡ true 
  → Σ[ pds1 ∈ List (X → Bool) ] 
     Σ[ pds2 ∈ List (X → Bool) ] 
     Σ[ p ∈ (X → Bool) ] 
     pds1 ++ p ∷ pds2 ≡ pds × 
     isMatched x pds1 ≡ false × 
     p x ≡ true
isMatchedSound x [] ()
isMatchedSound x (x₁ ∷ pds) cp with inspect (x₁ x) 
isMatchedSound x (x₁ ∷ pds) cp 
  | it true x₂ rewrite x₂ = [] , pds , x₁ , refl , refl , x₂
isMatchedSound x (x₁ ∷ pds) cp 
  | it false x₂ with isMatchedSound x pds 
    (subst (λ h → h ∨ foldr _∨_ false (map (λ p → p x) pds) ≡ true) x₂  cp)
... | o1 , o2 , o3 , o4 , o5 , o6 = x₁ ∷ o1 , o2 , o3 ,
     trans (cong (_∷_ x₁) o4) refl , h , o6
  where
    h : x₁ x ∨ isMatched x o1 ≡ false
    h = subst (λ h → h ∨ isMatched x o1 ≡ false) (sym x₂) o5   

isMatchedComplete : {X : Set} → (xs : List X) → (pds : List (X → Bool))  
 → ∀ x → x ∈ xs
 →  Σ[ p ∈ (X → Bool) ] p ∈ pds × p x ≡ true
 → isMatched x pds ≡ true
isMatchedComplete xs [] x xin (p1 , () , p3)
isMatchedComplete xs (x ∷ pds) x₁ xin (.x , here , p3) rewrite p3 = refl
isMatchedComplete xs (x ∷ pds) x₁ xin (x₂ , there p2 , p3) with x x₁ 
... | false = isMatchedComplete xs pds x₁ xin (x₂ , p2 , p3)
... | true = refl


allMatched : {X : Set} → List X → List (X → Bool) → Bool
allMatched xs pds = all (λ x → isMatched x pds) xs


allMatchedSplit : {X : Set} → (xs ys : List X) → (pds : List (X → Bool))
  → allMatched (xs ++ ys) pds ≡ allMatched xs pds ∧ allMatched ys pds
allMatchedSplit [] ys pds = refl
allMatchedSplit (x ∷ xs) ys pds 
  rewrite allMatchedSplit xs ys pds 
  = ∧-assoc (isMatched x pds) (allMatched xs pds) (allMatched ys pds)


allMatchedSound : {X : Set} → (xs : List X) → (pds : List (X → Bool))
 → allMatched xs pds ≡ true
 → ∀ x → x ∈ xs 
 → Σ[ pds1 ∈ List (X → Bool) ] 
    Σ[ pds2 ∈ List (X → Bool) ] 
    Σ[ p ∈ (X → Bool) ] 
    pds1 ++ p ∷ pds2 ≡ pds × 
    isMatched x pds1 ≡ false × 
    p x ≡ true
allMatchedSound xs pds pr x xin with ∃-split x xs xin 
... | o1 , o2 , o3 
  rewrite o3 | allMatchedSplit o1 (x ∷ o2) pds 
  with allMatched o1 pds 
allMatchedSound xs pds pr x xin | o1 , o2 , o3 
  | true with allMatched o2 pds  
allMatchedSound xs pds pr x xin | o1 , o2 , o3 
  | true | true rewrite ∧-comm (isMatched x pds) true 
  = isMatchedSound x pds pr
allMatchedSound xs pds pr x xin | o1 , o2 , o3 
  | true | false rewrite ∧-comm (isMatched x pds) false  with pr
... | () 
allMatchedSound xs pds () x xin | o1 , o2 , o3 | false


allMatchedComplete : {X : Set} → (xs : List X) → (pds : List (X → Bool))
 → (∀ x → x ∈ xs → Σ[ p ∈ (X → Bool) ] p ∈ pds × p x ≡ true)
 → allMatched xs pds ≡ true
allMatchedComplete [] pds prop = refl
allMatchedComplete (x ∷ xs) pds prop 
  rewrite isMatchedComplete (x ∷ xs) pds x here (prop x here)
  = allMatchedComplete xs pds (λ x' x'in → prop x' (there x'in)) 


unmatched : {X : Set} → List X → List (X → Bool) → List X
unmatched [] l = []
unmatched (x ∷ xs) l = if (isMatched x l) 
                         then unmatched xs l 
                         else x ∷ (unmatched xs l)


unmatchedComplete' : {X : Set} → (xs : List X) → (ps : List (X → Bool)) 
  → allMatched xs ps ≡ true
  → unmatched xs ps ≡ []  
unmatchedComplete' [] ps pr = refl
unmatchedComplete' (x ∷ xs) ps pr with isMatched x ps 
unmatchedComplete' (x ∷ xs) ps pr | true = unmatchedComplete' xs ps pr
unmatchedComplete' (x ∷ xs) ps () | false


unmatchedComplete : {X : Set} → (xs : List X) → (ps : List (X → Bool))
 → (∀ x → x ∈ xs → Σ[ p ∈ (X → Bool) ] p ∈ ps × p x ≡ true)
 → unmatched xs ps ≡ []
unmatchedComplete xs ps prop 
  = unmatchedComplete' xs ps 
     (allMatchedComplete xs ps prop)



unmatchedSound' : {X : Set} → (xs : List X) → (ps : List (X → Bool)) 
  → unmatched xs ps ≡ [] 
  → allMatched xs ps ≡ true
unmatchedSound' [] ps pr = refl
unmatchedSound' (x ∷ xs) ps pr with isMatched x ps
unmatchedSound' (x ∷ xs) ps pr | true = unmatchedSound' xs ps pr
unmatchedSound' (x ∷ xs) ps () | false


unmatchedSound : {X : Set} → (xs : List X) → (ps : List (X → Bool))
 → unmatched xs ps ≡ []
 → ∀ x → x ∈ xs 
 → Σ[ ps1 ∈ List (X → Bool) ] 
    Σ[ ps2 ∈ List (X → Bool) ] 
    Σ[ p ∈ (X → Bool) ] 
    ps1 ++ p ∷ ps2 ≡ ps × 
    isMatched x ps1 ≡ false × 
    p x ≡ true
unmatchedSound xs ps pr x xin 
  = allMatchedSound xs ps 
     (unmatchedSound' xs ps pr) x xin


predicateMatching : {X Y : Set} → (kf : Listable X) 
  → (eqs : List ((X → Bool) × (X → Y)) ) 
  → unmatched (proj₁ kf) (map proj₁ eqs) ≡ []
  → X → Y
predicateMatching (l , lpr) eqs pr x  
  with unmatchedSound l (map proj₁ eqs) pr x (lpr x) 
... | o1 , o2 , o3 , o4 , o5 , o6 
  with ∃-after-map2 proj₁ eqs o1 (o3 ∷ o2) (sym o4) 
predicateMatching (l , lpr) eqs pr x 
  | o1 , o2 , o3 , o4 , o5 , o6 
  | p1 , [] , p3 , p4 , ()
predicateMatching (l , lpr) eqs pr x₁ 
  | o1 , o2 , o3 , o4 , o5 , o6 
  | p1 , (pred , func) ∷ p2 , p3 , p4 , p5 = func x₁


predicateMatchingSound : {X Y : Set} → (kf : Listable X) 
  → (eqs : List ((X → Bool) × (X → Y))) 
  → (pr : unmatched (proj₁ kf) (map proj₁ eqs) ≡ [])
  → ∀ x y 
  → predicateMatching kf eqs pr x ≡ y
  → Σ[ ps1 ∈ List ((X → Bool) × (X → Y)) ] 
     Σ[ ps2 ∈ List ((X → Bool) × (X → Y)) ] 
     Σ[ p ∈ ((X → Bool) × (X → Y)) ] 
     ps1 ++ p ∷ ps2 ≡ eqs × 
     isMatched x (map proj₁ ps1) ≡ false  ×
     (proj₁ p) x ≡ true ×
     (proj₂ p) x ≡ y
predicateMatchingSound (l , lpr) eqs pr x y eq 
  with unmatchedSound l (map proj₁ eqs) pr x (lpr x) 
... | o1 , o2 , o3 , o4 , o5 , o6 
  with ∃-after-map2 proj₁ eqs o1 (o3 ∷ o2) (sym o4) 
predicateMatchingSound (l , lpr) eqs pr x y eq 
  | o1 , o2 , o3 , o4 , o5 , o6 | p1 , [] , p3 , p4 , ()
predicateMatchingSound (l , lpr) eqs pr x₁ y eq 
  | o1 , o2 , o3 , o4 , o5 , o6 
  | p1 , (p , f) ∷ p2 , p3 , p4 , p5 
  = p1 , p2 , (p , f) ,  p3 , 
   subst (λ h → isMatched x₁ h ≡ false) (sym p4) o5 , 
    subst (λ h → h x₁ ≡ true) 
          (sym ((cong (λ { (z ∷ zs) → z ; [] → o3 }) p5))) o6 , eq


isMatchedSimpl : {X Y : Set} → (ls1 : List ((X → Bool) × (X → Y))) → ∀ x
 → isMatched x (map proj₁ ls1) ≡ any (λ l → (proj₁ l) x) ls1
isMatchedSimpl [] x = refl
isMatchedSimpl ((proj₁ , proj₂) ∷ ls1) x₁ with proj₁ x₁ 
isMatchedSimpl ((proj₁ , proj₂) ∷ ls1) x₁ | true = refl
isMatchedSimpl ((proj₁ , proj₂) ∷ ls1) x₁ | false = isMatchedSimpl ls1 x₁


predicateMatchingComplete : {X Y : Set} → (kf : Listable X) 
  → (pds1 pds2 : List ((X → Bool) × (X → Y)))
  → (p : (X → Bool))
  → (fun : (X → Y))
  → (pr : unmatched (proj₁ kf) (map proj₁ (pds1 ++ (p , fun) ∷ pds2)) ≡ [])
  → ∀ x
  → isMatched x (map proj₁ pds1) ≡ false 
  → p x ≡ true
  → predicateMatching kf (pds1 ++ (p , fun) ∷ pds2) pr x ≡ fun x
predicateMatchingComplete kf pds1 pds2 p fun pr x ch px 
  with predicateMatchingSound kf  (pds1 ++ (p , fun) ∷ pds2) pr x 
  (predicateMatching kf (pds1 ++ (p , fun) ∷ pds2) pr x) refl 
... | ls1 , ls2 , (ls31 , ls32) , ls4 , ls5 , ls6 , ls7  
  rewrite isMatchedSimpl pds1 x 
  | isMatchedSimpl ls1 x 
  with any-prop (λ l → proj₁ l x) ls1 ls2  pds1 pds2 (p , fun) 
         (ls31 , ls32) ls4 ls5 ch ls6 px 
... | ap rewrite ap 
  with cong (λ { (z ∷ zs) → z ; [] → (ls31 , ls32) }) 
            (list-= pds1 ((ls31 , ls32) ∷ ls2) ((p , fun) ∷ pds2) ls4)
... | eqp = subst (λ h → _ ≡ h x) ( (cong proj₂ eqp)) (sym ls7)


record PredicateMatching  (X : Set) (Y : Set) : Set where
  field
   match  : List ((X → Bool) × (X → Y))
   finDom : Listable X
   unreachedCheck : (unreached (map proj₁ match) (proj₁ finDom)) ≡ []
   unmatchedCheck : (unmatched  (proj₁ finDom) (map proj₁ match)) ≡ [] 
open PredicateMatching  public


open import FiniteSubset
open import Tabulation

PMtofun : {X Y : Set} → PredicateMatching X Y → X → Y
PMtofun p = predicateMatching (finDom p) (match p) (unmatchedCheck p)


makePM : {X Y : Set}{eq : DecEq X}{b : Bool} → (f : FiniteSubSet X eq b) 
  → (match : List ((Element f → Bool) × (Element f → Y)) )
  → (unreached (map proj₁ match) (elementsOf f)) ≡ []
  → (unmatched (elementsOf f) (map proj₁ match)) ≡ []
  → PredicateMatching (Element f) Y
makePM f match pr1 pr2 = record {
     match = match ;
     finDom = elementsOf f , elementsOfComplete f ;
     unreachedCheck = pr1 ;
     unmatchedCheck = pr2 
   }

