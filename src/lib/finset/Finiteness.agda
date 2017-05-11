

module Finiteness where

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Data.Bool hiding (_≟_)
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map ; All)
open import Data.List
open import Data.Fin 
  hiding ( _≤_ ; _<_) 
  renaming (suc to fsuc ; zero to fzero ; pred to fpred)
open import Data.Empty 
open import Data.Nat hiding (_⊔_)
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Vec 
  renaming (map to vmap ; _∈_ to _∈v_ ; _++_ to _++v_ ; _∷_ to _::_) 
  hiding (drop ; take ; foldl ; foldr)  

open import Function

open import Level hiding (suc ; zero)

open import Data.Vec.Properties hiding (map-cong)

open import Utilities.NatProperties
open import Utilities.VecProperties
open import Utilities.FinProperties
open import Utilities.BoolProperties
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic




All : {a : Level} {X : Set a} → List X → Set a
All xs = ∀ x → x ∈ xs


FinBij : (X : Set) → Set
FinBij X = Σ[ n ∈ ℕ ] 
           Σ[ toFin ∈ (X → Fin n) ] 
           Σ[ fromFin ∈ (Fin n → X) ]
           (∀ x → fromFin (toFin x) ≡ x) ×
           (∀ f → toFin (fromFin f) ≡ f)


ListableNoDup : (X : Set) → Set
ListableNoDup X = Σ[ xs ∈ List X ]
                  All xs ×
                  NoDupInd xs


FinSurj : (X : Set) → Set
FinSurj X = Σ[ n ∈ ℕ ] 
            Σ[ toFin   ∈ (X → Fin n) ]
            Σ[ fromFin ∈ (Fin n → X) ]
            (∀ x → fromFin (toFin x) ≡ x)


Listable : ∀{a} → (X : Set a) → Set a
Listable X = Σ[ xs ∈ List X ]
             All xs 


ListableSubfinite : {a : Level} → (X : Set a) → (X → Set a) → Set a
ListableSubfinite X P = Σ[ xs ∈ List X ] 
                        (∀ x → P x → x ∈ xs)

-- upper bound on cardinality of subfinite listable sets
⌈_⌉ : {X : Set} → {P : X → Set} → ListableSubfinite X P → ℕ
⌈ xs , _ ⌉ = length xs


ListableSubset : {a b : Level} → (X : Set a) → (X → Set b) → Set (a ⊔ b)
ListableSubset X P = Σ[ xs ∈ List X ] 
                     (∀ x → x ∈ xs → P x) × 
                     (∀ x → P x → x ∈ xs)

-- listable subsets could be checked for emptiness
isEmpty? : {X : Set} → {P : X → Set} → ListableSubset X P → Bool
isEmpty? ([] , _ ) = true
isEmpty? (_  , _ ) = false


vnd : {X : Set} → {n : ℕ}  → (v : Vec X n) 
  → ((i j : Fin n) → lookup i v ≡ lookup j v → i ≡ j) → NoDupInd (toList v)
vnd [] pr = end
vnd {n = (suc n)} (x :: v) pr = hlp ::: vnd  v hlp2
  where
    hlp : ¬ x ∈ toList v
    hlp pr'' with ∈∈v2 x v (∈∈v x v pr'') 
    ... | f , lk with pr fzero (fsuc f) (sym lk) 
    ... | ()

    hlp2 : (i j : Fin n) → lookup i v ≡ lookup j v → i ≡ j
    hlp2 i j prf = fsucl _ _ (pr (fsuc i) (fsuc j) prf)
      where
        fsucl : {n : ℕ} → (i j : Fin n) → fsuc i ≡ fsuc j → i ≡ j
        fsucl i .i refl = refl



nodupallfin : ∀ n → NoDupInd (allFinList n)
nodupallfin n =  vnd (allFin n) hlp
  where
    hlp : (i j : Fin n) → lookup i (allFin n) ≡ lookup j (allFin n) → i ≡ j
    hlp i j pr rewrite lookup-allFin i | lookup-allFin j = pr



all2 : {X Y : Set} → (f : Y → X) → (t : X → Y) → (l : List Y) 
  → (∀ x → f (t x) ≡ x) 
   → All l → All (map f l)
all2 f t l pr all x with all (t x) 
... | o with ∃-split (t x) l o 
... | ds1 , fs2 , pr' rewrite pr' | maphom ds1 (t x ∷ fs2) f | pr x 
  = ∈-weak-lft {_} {map f ds1} {x ∷ map f fs2} {x} here 

nd2 : {X Y : Set} → (f : Y → X) → (t : X → Y) → (l : List Y) 
  → (∀ y → t (f y) ≡ y)  
  → NoDupInd l → NoDupInd (map f l)
nd2 f t .[] pr end = end
nd2 f t ._ pr (x₁ ::: nd) 
   = (λ pr' → x₁ (map-cong2 f t pr _ _ pr' )) ::: nd2 f t _ pr nd

nd2' : {X Y : Set} → (f : Y → X)  → (l : List Y) 
  → (∀ y1 y2 → f y1 ≡ f y2 → y1 ≡ y2)  
  → NoDupInd l → NoDupInd (map f l)
nd2' f  .[] pr end = end
nd2' f  ._ pr (x₁ ::: nd) 
   = (λ pr' → x₁ (map-cong3 f  pr _ _ pr' )) ::: nd2' f _ pr nd

bij2nodup : {X : Set} → FinBij X → ListableNoDup X
bij2nodup {X} (n , toFin , fromFin , inv1 , inv2) = 
    map fromFin (allFinList n) 
  , all2 fromFin toFin _ inv1 (allFinListComplete n) 
  , nd2 fromFin toFin (allFinList n) inv2 (nodupallfin n)




nodup2bij : {X : Set} → ListableNoDup X → FinBij X 
nodup2bij {X} (xs , all , nd) = length xs , toFin , fromFin , inv1 , inv2

  where
    toFin : X → Fin (length xs)
    toFin x = convf xs (x , all x)

    fromFin : Fin (length xs) → X
    fromFin x = proj₁ (convb xs x) 

    inv1 : (x : X) → fromFin (toFin x) ≡ x
    inv1 x rewrite convbf xs (x , all x) = refl

    inv2 : (y : Fin (length xs)) → toFin (fromFin y) ≡ y
    inv2 y with inspect (convb xs y)
    ... | it (q1 , q2) p  rewrite p | NoDupInd-pr  q1 xs (all q1) q2 nd 
     = subst (λ h → convf xs h ≡ y) p (convfb xs y)



surj2lstbl : {X : Set} → FinSurj X → Listable X
surj2lstbl {X} (n , toFin , fromFin , inv)  = 
  map fromFin (allFinList n)  
  , all2 fromFin toFin _ inv (allFinListComplete n) 


lstbl2surj : {X : Set} → Listable X → FinSurj X
lstbl2surj {X} (xs , all) = length xs , toFin , fromFin , inv
  where
    toFin : X → Fin (length xs)
    toFin x = convf xs (x , all x)

    fromFin : Fin (length xs) → X
    fromFin x = proj₁ (convb xs x) 

    inv : (x : X) → fromFin (toFin x) ≡ x
    inv x rewrite convbf xs (x , all x) = refl




lstbl2subset : ∀{d} → {X : Set d} → Listable X → ListableSubset X (λ _ → ⊤)
lstbl2subset (xs , allxs) = xs , (λ _ _ → tt) , (λ x _ →  allxs x)


subset2lstbl : {X : Set} → ListableSubset X (λ _ → ⊤) → Listable X
subset2lstbl  (xs , snd , cmplt) = xs , (λ x → cmplt x tt)


subset2lstblGen : {X : Set} 
   → (P : X → Set) 
   → (Ppr : ∀ x → (p1 p2 : P x) → p1 ≡ p2) 
   → ListableSubset X P 
   → Listable (Σ[ x ∈ X ] P x)
subset2lstblGen P pr (xs , p1 , p2) = map-in xs 
  (λ p → proj₁ p , p1 _ (proj₂ p)) , hlp 
  where
    hlp : ∀ x → x ∈ map-in xs (λ p → proj₁ p , p1 (proj₁ p) (proj₂ p))
    hlp (x , pp) with map-in-pr xs (λ p → proj₁ p , p1 (proj₁ p) (proj₂ p)) x 
                                   (p2 x pp) 
    ... | (xi1 , xi2) rewrite pr x (p1 x xi1) pp = xi2


lstbl2subsetGen : {X : Set} 
   → (P : X → Set) 
   → (Ppr : ∀ x → (p1 p2 : P x) → p1 ≡ p2) 
   → Listable (Σ[ x ∈ X ] P x)
   → ListableSubset X P 
lstbl2subsetGen {X} P pr (xs , all) = map proj₁ xs , hlp , 
   (λ x px → ∃-after-map _ _ proj₁ (all (x , px)))
  where
   hlp : (x : X) → x ∈ map (λ r → proj₁ r) xs → P x
   hlp x xi with map∃' x proj₁ xs xi 
   hlp x xi | (.x , px) , o2 , refl = px


private
  helper : {X : Set}  
    → ∀ x' 
    → (P : X → Set) → (Ppr : ∀ x → (p1 p2 : P x) → p1 ≡ p2) (x1' x2' : X) 
    → (xs'' p1' p2' q1' q2' : List X)
    → (from : (x : X) → P x → x ∈ (p1' ++ x1' ∷ p2'))
    → (q3'      : p1' ++ x1' ∷ p2' ≡ (p1' ++ x' ∷ xs'') ++ x2' ∷ q2')
    → (px1' : P x1') → (px2' : P x2')
    → (x2in'    : x2' ∈ (p1' ++ x1' ∷ p2'))
    → (x1in'    : x1' ∈ (p1' ++ x1' ∷ p2'))
    → (x1inprf' : from x1' px1' ≡ x1in')
    → (x2inprf' : from x2' px2' ≡ x2in')
    → ∃-split x2' (p1' ++ x1' ∷ p2') x2in' ≡ (p1' ++ x' ∷ xs'' , q2' , q3')
    → ∃-split x1' (p1' ++ x1' ∷ p2') x1in' ≡ (p1' , p2' , refl)
    → x1' ≡ x2'
    → ⊥
  helper x' P Ppr x3 .x3 xs'' p4 p5 q4 q5 from' q6 px3 
    px4 x2in₁ x1in₁ x1inpr x2inpr sp1 sp2 refl with Ppr x3 px3 px4
  helper x' P Ppr x3 .x3 xs'' p4 p5 q4 q5 from' q6 px3 
    .px3 .(from' x3 px3) .(from' x3 px3) refl refl sp1 sp2 refl | refl
     = list-⊥ _ _ _ (cong proj₁ (trans (sym sp2) sp1)) 


equality1 : {X : Set} 
   → (P : X → Set) 
   → (Ppr : ∀ x → (p1 p2 : P x) → p1 ≡ p2) 
   → ListableSubset X P 
   → DecEqRest P
equality1 P Ppr (list , to , from) x1 x2 px1 px2 
  with inspect (from x1 px1) | inspect (from x2 px2)
... | it x1in x1inprf | it x2in x2inprf 
  with inspect (∃-split x1 list x1in) | inspect (∃-split x2 list x2in)
... | it (p1 , p2 , p3) pprf  | it (q1 , q2 , q3) qprf  
  with ≤-pr' (length p1) (length q1) 
... | inj₁ p1<q1  with list-div (length p1) (length q1) list p1<q1 
... | (xs' , prf) rewrite p3 | take-prop p1 (x1 ∷ p2)
  with subst (λ h → take (length q1) h ≡ p1 ++ xs') q3 prf 
... | eq1 rewrite take-prop q1 (x2 ∷ q2) with xs'
... | [] rewrite ++-[] p1 | eq1 =   
  yes (cong (λ { (z ∷ zs) → z ; [] → x1 }) 
       (len-=2 p1 (x1 ∷ p2) p1 (x2 ∷ q2) q3 refl))
... | (x' ∷ xs'') rewrite eq1 = 
  no 
  (λ x1≡x2 → helper x' P Ppr x1 x2 xs'' p1 p2 q1 q2 from q3 px1 px2 
                     x2in x1in x1inprf x2inprf qprf pprf x1≡x2)


equality1 P Ppr  (list , to , from) x1 x2 px1 px2 
  | it x1in x1inprf | it x2in x2inprf 
  | it (p1 , p2 , p3) pprf | it (q1 , q2 , q3) qprf 
  | inj₂ p1<q1 
  with list-div (length q1) (length p1) list p1<q1 
... | (xs' , prf) rewrite q3 | take-prop q1 (x2 ∷ q2) 
  with subst (λ h → take (length p1) h ≡ q1 ++ xs') p3 prf 
... | eq1 rewrite  take-prop p1 (x1 ∷ p2) with xs'
... | [] rewrite ++-[] q1 | eq1 
  = yes (cong (λ { (z ∷ zs) → z ; [] → x1 }) 
              (len-=2 q1 (x1 ∷ p2) q1 (x2 ∷ q2) (sym p3) refl))
... | (x' ∷ xs'') rewrite eq1 
  = no (λ x1≡x2 → helper x' P Ppr x2 x1 xs'' q1 q2 p1 p2 from p3 px2 
                          px1 x1in x2in x2inprf x1inprf pprf qprf (sym x1≡x2))


equality1' : {X : Set} 
   → (P : X → Set) 
   → (Ppr : ∀ x → (p1 p2 : P x) → p1 ≡ p2) 
   → ListableSubset X P 
   → DecEq (Σ[ x ∈ X ] P x)
equality1' P pr ls (x1 , px1) (x2 , px2) 
  with equality1 P pr ls x1 x2 px1 px2 
equality1' P pr ls (x1 , px1) (.x1 , px2) | yes refl 
  rewrite pr x1 px1 px2 = yes refl
equality1' P pr ls (x1 , px1) (x2 , px2) | no ¬p = no $ λ pr 
  → ¬p $ cong proj₁ pr


equality2 : {X : Set} 
   → (P : X → Set) 
   → (kf : ListableSubset X P)
   → NoDupInd (proj₁ kf)
   → ∀ x₁ x₂ → P x₁ → P x₂ → Dec (x₁ ≡ x₂)
equality2 {X} P (els1 , i2p , p2i) nd x1 x2 px1 px2 
  = equality1 (λ x → x ∈ els1) 
       (λ x xin1 xin2 → NoDupInd-pr x els1 xin1 xin2 nd) 
       kf' x1 x2 (p2i x1 px1) (p2i x2 px2)
   where
     kf' : ListableSubset X (λ x → x ∈ els1)
     kf' = els1 , (λ x i → i) , (λ x i → i)


equality3 : {X : Set}  
   → (P : X → Set) 
   → (kf : ListableSubset X P)
   → (decP : ∀ x → Dec (P x))
   → ∀ x₁ x₂ → P x₁ → P x₂ → Dec (x₁ ≡ x₂)
equality3 {X} P (els , i2p , p2i) d x1 x2 px1 px2 
  = equality1 _ pr kf' x1 x2 (∥-∥-prop2 px1 (d x1)) (∥-∥-prop2 px2 (d x2)) 
  where
     kf' : ListableSubset X (λ x → ∥ d x ∥ )
     kf' = els , (λ x xin → ∥-∥-prop2 (i2p x xin) (d x)) , 
                 (λ x dx → p2i x (∥-∥-prop3 (d x) dx))

     pr : ∀ x →  (p1 p2 : ∥ d x ∥) → p1 ≡ p2
     pr x p1 p2 = ∥-∥-prop (d x) p1 p2


lstblEq : {X : Set} → Listable X → DecEq X
lstblEq lstbl x₁ x₂ = equality1 (λ _ → ⊤) (λ { _ tt tt → refl}) 
   (lstbl2subset lstbl) x₁ x₂ tt tt


lstblNoDupEq : {X : Set} → ListableNoDup X → DecEq X
lstblNoDupEq (xs , allxs , ndxs) = lstblEq (xs , allxs) 


lstbl2nodup : {X : Set} → Listable X → ListableNoDup X
lstbl2nodup  (xs , allxs) = 
   remDup ∈? xs , 
   (λ x → remDupSound ∈? x xs (allxs x)) , 
   NoDupInd-corr2 _ ((remDupCorrect ∈? xs))
     where 
       ∈? = eq2in (lstblEq (xs , allxs))


nodup2lstbl : {X : Set} → ListableNoDup X → Listable X
nodup2lstbl (xs , all , _) = (xs , all)

-- exact cardinality of listable set
∣_∣ : {X : Set} → Listable X → ℕ
∣_∣ lstbl = length ∘ proj₁ $ lstbl2nodup lstbl

