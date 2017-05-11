
module Utilities.ListProperties where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_] ; inspect)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Nat hiding (_<_)
open import Utilities.Logic
open import Utilities.ArithmeticProperties
open import Data.Sum hiding (map)
open import Level hiding (suc)

infix 5 _∈_
data _∈_ {a} {A : Set a} : A → List A → Set a where
  here  : ∀ {x}   {xs : List A} → x ∈ (x ∷ xs)
  there : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) → x ∈ (y ∷ xs)

DecIn : ∀ X → Set
DecIn X = Decidable (_∈_ {A = X})

eq2in : {X : Set} → DecEq X → DecIn X
eq2in d x [] = no (λ { () })
eq2in d x (x₁ ∷ xs) with d x x₁ 
eq2in d x (.x ∷ xs) | yes refl = yes here
eq2in d x (x₁ ∷ xs) | no ¬p with eq2in d x xs 
eq2in d x (x₁ ∷ xs) | no ¬p | yes p = yes (there p)
eq2in d x (x₁ ∷ xs) | no ¬p₁ | no ¬p = no (λ prin2 → f _ _ _ ¬p₁ ¬p prin2)
 where
   f : {A : Set} → (x x₁ : A) → (xs : List A) → (x ≡ x₁ → ⊥) → ¬ x ∈ xs → ¬ x ∈ (x₁ ∷ xs)
   f x₂ .x₂ xs₁ pr prin here = pr refl
   f x₂ x₃ xs₁ pr prin (there prin2) = prin prin2


in2eq : {X : Set} → DecIn X → DecEq X
in2eq ∈?  x1 y1  with ∈? x1  (y1 ∷ []) 
in2eq ∈? x1 .x1 | yes here = yes refl
in2eq ∈? x1 y1 | yes (there ())
in2eq ∈? x1 y1 | no ¬p = no (λ pr → ¬p (subst (λ h → x1 ∈ (h ∷ [])) pr here))


infixr 5 _:::_
data NoDupInd {X : Set} : List X → Set where
  end : NoDupInd []
  _:::_ : {xs : List X} → {x : X} → (¬ x ∈ xs) 
           → NoDupInd xs → NoDupInd (x ∷ xs)



NoDup : {a : Level} {X : Set a} → List X → Set a
NoDup {X = X} xs = (x : X) → x ∈ xs → Σ[ ys ∈ List X ] 
                                    Σ[ zs ∈ List X ] 
                                    xs ≡ ys ++ x ∷ zs × 
                                    ¬ x ∈ ys × 
                                    ¬ x ∈ zs


NoDupInd-corr : {X : Set} → (xs : List X) → NoDupInd xs → NoDup xs
NoDupInd-corr [] nde x ()
NoDupInd-corr (x ∷ xs) (_:::_ .{xs} .{x} x₁ ndxs) .x here = [] , xs , refl , (λ { ( ) }) , x₁
NoDupInd-corr (x ∷ xs) (_:::_ .{xs} .{x} x₁ ndxs) x₂ (there x₃) with NoDupInd-corr xs ndxs x₂ x₃ 
... | o1 , o2 , o3 , o4 , o5 = x ∷ o1 , o2 , cong (_∷_ x) o3 , h x x₂ xs o1 x₃ x₁  o4 , o5
  where
    h : {X : Set} → (x x₂ : X) → (xs o1 : List X) 
     → x₂ ∈ xs → (x ∈ xs → ⊥) → (x₂ ∈ o1 → ⊥) →  x₂ ∈ (x ∷ o1) → ⊥
    h x₄ .x₄ xs₁ o6 xin xinn xinn2 here = xinn xin
    h x₄ x₅ xs₁ o6 xin xinn xinn2 (there xin2) = xinn2 xin2


NoDupInd-pr : {X : Set} → (x : X) → (xs : List X) → (p1 p2 : x ∈ xs) → NoDupInd xs → p1 ≡ p2
NoDupInd-pr x .[] () p2 end
NoDupInd-pr x ._ here here (x₂ ::: md) = refl
NoDupInd-pr x ._ here (there p2) (x₂ ::: md) with x₂ p2 
... | ()
NoDupInd-pr x₁ ._ (there p1) here (x₂ ::: md) with x₂ p1
... | ()
NoDupInd-pr x ._ (there p1) (there p2) (x₂ ::: md) = cong there (NoDupInd-pr x _ p1 p2 md)

lem : {X : Set} → (x : X) → (xs ys ps : List X)
  →  x ∷ xs ≡ ys ++ x ∷ ps → (x ∈ ys → ⊥) → ys ≡ []
lem x xs [] ps pr1 pr2 = refl
lem x xs (x₁ ∷ ys) ps pr1 pr2 with cong (take 1) pr1 
lem x xs (.x ∷ ys) ps pr1 pr2 | refl with pr2 here
... | ()

NoDupInd-corr2' : {X : Set} → (xs : List X) → ∀ x → NoDup (x ∷ xs) → NoDup xs 
NoDupInd-corr2' xs x nd  p pin with nd p (there pin)
NoDupInd-corr2' xs x nd .x pin | [] , .xs , refl , q4 , q5 with q5 pin 
... | ()
NoDupInd-corr2' .(q1 ++ p ∷ q2) x nd p pin | .x ∷ q1 , q2 , refl , q4 , q5 = q1 , q2 , refl , (λ pi → q4 (there pi)) , q5

NoDupInd-corr2 : {X : Set} → (xs : List X) → NoDup xs → NoDupInd xs
NoDupInd-corr2 [] nd = end
NoDupInd-corr2 (x ∷ xs) nd with nd x here 
... | ys , ps , z1 , z2 , z3 with lem x xs ys ps z1 z2 
... | ro rewrite ro =  (λ pr → z3 (subst (λ h → x ∈ h) (cong (drop 1) z1) pr)) ::: NoDupInd-corr2 _ (NoDupInd-corr2' xs x nd)





list-= : {X : Set} → (p1 o2 o3 : List X) 
 → p1 ++ o2 ≡ p1 ++ o3 → o2 ≡ o3
list-= [] o2 o3 pr = pr
list-= (x ∷ p1) o2 o3 pr = list-= p1 o2 o3 (cong (drop 1) pr)


list-eq : {C : Set} → Decidable (_≡_ {A = C}) → Decidable (_≡_ {A = List C})
list-eq d [] [] = yes refl
list-eq d [] (x ∷ ys) = no (λ { () })
list-eq d (x ∷ xs) [] = no (λ { () })
list-eq d (x ∷ xs) (x₁ ∷ ys) with d x x₁ 
list-eq d (x ∷ xs) (.x ∷ ys) | yes refl with list-eq d xs ys 
list-eq d (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
list-eq d (x ∷ xs) (.x ∷ ys) | yes refl | no ¬p = no (λ pr → ¬p (cong (drop 1) pr))
list-eq d (x ∷ xs) (x₁ ∷ ys) | no ¬p = no (λ pr → ¬p (cong (λ { (z ∷ zs) → z ; _ → x }) pr))



eq-cons : {X : Set} → (x y : X) → (xs ys : List X) → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
eq-cons x .x xs .xs refl = refl



∃-after-map2 : {X Y : Set} → (f : X → Y) → (xs : List X) → (ys1 ys2 : List Y)
  → map f xs ≡ ys1 ++ ys2
  →  Σ[ xs1 ∈ List X ] Σ[ xs2 ∈ List X ] xs1 ++ xs2 ≡ xs × map f xs1 ≡ ys1 × map f xs2 ≡ ys2
∃-after-map2 f xs [] ys2 meq = [] , xs , refl , refl , meq
∃-after-map2 f [] (x ∷ ys1) ys2 ()
∃-after-map2 f (x ∷ xs) (x₁ ∷ ys1) ys2 meq with ∃-after-map2 f xs ys1 ys2 (cong (drop 1) meq) 
... | xs1 , xs2 , xseq , yseq1 , yseq2 with eq-cons (f x) x₁ (map f xs) (ys1 ++ ys2) meq 
... | eq rewrite eq = x ∷ xs1 , xs2 , cong (_∷_ x) xseq , h , yseq2
   where
     h : f x ∷ map f xs1 ≡ x₁ ∷ ys1
     h  = subst (λ h → h ∷ map f xs1 ≡ x₁ ∷ ys1) (sym eq) (cong (_∷_ x₁) yseq1) 



maphom : {A B : Set} → (xs ys : List A) → (f : A → B) →  map f (xs ++ ys) ≡ map f xs ++ map f ys
maphom [] ys f = refl
maphom (x ∷ xs) ys f = cong (_∷_ _) (maphom xs ys f) 

++-assoc : {A : Set} → (a b c : List A) → a ++ b ++ c ≡ (a ++ b) ++ c
++-assoc [] b c = refl
++-assoc (x ∷ a) b c = cong (_∷_ x) (++-assoc a b c)

++-rgt-id : {X : Set}(xs : List X) →  xs ++ [] ≡ xs
++-rgt-id [] = refl
++-rgt-id (x ∷ xs) = cong (_∷_ x) (++-rgt-id xs )



∈len : {X : Set} → {x : X} → {xs : List X} → x ∈ xs → ℕ
∈len here = 0
∈len (there p) = 1 + ∈len p

∈lenlem : {X : Set} → {x : X} → {xs : List X} 
  → (p1 p2 : x ∈ xs) 
  → ∈len p1 ≡ ∈len p2 → p1 ≡ p2
∈lenlem here here prf = refl
∈lenlem here (there p2) ()
∈lenlem (there p1) here ()
∈lenlem (there p1) (there p2) prf 
  rewrite ∈lenlem p1 p2  (cong pred prf) = refl

∈-cong : {X Y : Set} → (x : X) → (xs : List X) → (f : X → Y) → x ∈ xs → f x ∈ map f xs
∈-cong x .(x ∷ xs) f (here {.x} {xs}) = here
∈-cong x .(y ∷ xs) f (there {.x} {y} {xs} xin) = there (∈-cong x xs f xin)

∈-weak-lft : {X : Set}{xs₁ xs₂ : List X}{x : X} → x ∈ xs₂ 
 → x ∈ (xs₁ ++ xs₂)
∈-weak-lft {X} {[]} xin = xin
∈-weak-lft {X} {x ∷ xs₁} xin = there (∈-weak-lft {_} {xs₁} xin)


∈-weak-lft-pos : {X : Set}{x : X}(xs₁ xs₂ : List X)
 → (pin : x ∈ xs₂)
 → ∈len (∈-weak-lft {_} {xs₁} {xs₂} pin) ≡ (length xs₁) + (∈len pin)
∈-weak-lft-pos [] xs₂ pin = refl
∈-weak-lft-pos (x₁ ∷ xs₁) xs₂ pin = cong suc (∈-weak-lft-pos xs₁ xs₂  pin)

postulate ∈-weak-lft-pos' : {X : Set}{x : X}(xs₁ xs₂ : List X) → (pin : x ∈ xs₂) → ∈len (∈-weak-lft {_} {xs₁} {xs₂} pin) ≡ (∈len pin) + (length xs₁)



∈-weak-rgt : {X : Set}{b c : List X}{a : X} → a ∈ c → a ∈ (c ++ b)
∈-weak-rgt here = here
∈-weak-rgt (there i) = there (∈-weak-rgt i)

∈-split : {X : Set} →  {xs₁ xs₂ : List X} → {x : X}
 →  x ∈ (xs₁ ++ xs₂) 
 → (x ∈ xs₁) ⊎ (x ∈ xs₂)
∈-split {X} {[]} xin = inj₂ xin
∈-split {X} {x ∷ xs₁}  here = inj₁ here
∈-split {X} {x ∷ xs₁}  (there xin) with ∈-split {X} {xs₁} xin 
∈-split {X} {x₂ ∷ xs₁} (there xin) | inj₁ x₁ = inj₁ (there x₁)
∈-split {X} {x₁ ∷ xs₁} (there xin) | inj₂ y = inj₂ y


∃-after-map : {X Y : Set} → (d : X) →  (xs : List X) → (f : X → Y)
 → d ∈ xs → (f d) ∈ (map f xs)
∃-after-map d .(d ∷ xs) f (here {.d} {xs}) = here 
∃-after-map d .(y ∷ xs) f (there {.d} {y} {xs} x∈xs) = there (∃-after-map d xs f x∈xs)


∃-split : {X : Set}(x : X)(xs : List X) →  x ∈ xs 
  → Σ[ zs ∈ List X ] Σ[ ds ∈ List X ] xs ≡ zs ++ (x ∷ ds)
∃-split x .(x ∷ xs) (here {.x} {xs}) = [] , xs , refl
∃-split x .(y ∷ xs) (there {.x} {y} {xs} x∈xs) with ∃-split x xs x∈xs 
∃-split x .(y ∷ xs) (there {.x} {y} {xs} x∈xs) | proj₁ , proj₁' , proj₂ 
 = y ∷ proj₁ , proj₁' , cong (_∷_ y) proj₂

∃-split' : {X : Set}(x : X)(xs : List X) → (pin : x ∈ xs)
  → Σ[ zs ∈ List X ] 
    Σ[ ds ∈ List X ] 
     xs ≡ zs ++ (x ∷ ds) ×
     ∈len pin ≡ length zs
∃-split' x .(x ∷ xs) (here {.x} {xs}) = [] , xs , refl , refl
∃-split' x .(y ∷ xs) (there {.x} {y} {xs} pin) with ∃-split' x xs pin
... | p1 , p2 , p3 , p4 = y ∷ p1 , p2 , cong (_∷_ y) p3 , cong suc p4



∈-lst : {X : Set} → (xs : List X)  → List (Σ[ x ∈ X ] x ∈ xs )
∈-lst [] = []
∈-lst (x ∷ xs) 
 = (x , here) ∷ map (λ p → (proj₁ p , there (proj₂ p))) (∈-lst xs)

∈-lst-complete : ∀ {X} → (x : X) → (xs : List X) → (prf : (x ∈ xs)) → (x , prf) ∈ (∈-lst xs)
∈-lst-complete x [] ()
∈-lst-complete .x₁ (x₁ ∷ xs) here = here
∈-lst-complete x (x₁ ∷ xs)  (there prf) 
 = there (∈-cong (x , prf) 
         (∈-lst xs) 
         (λ {(p₁ , p₂) → (p₁ , there p₂)}) 
         (∈-lst-complete x xs prf))



foldl-unf : {A B : Set} → (ys : List B) → (l : List A) 
  → (f : A → List B)
  → foldl (λ res el → res ++ f el) ys l ≡ 
      ys ++ foldl (λ res el → res ++ f el  ) [] l
foldl-unf ys [] f =  sym (++-rgt-id _)
foldl-unf ys (x ∷ l) f rewrite 
 foldl-unf (ys ++ f x)  l f 
 | foldl-unf (f x) l f 
 = sym (++-assoc ys (f x) (foldl (λ res el → res ++ f el) [] l)) 


-- returning element from the list (with default value)
el : ∀ {X : Set} →  (i : ℕ) → (def : X) → List X → X
el n default [] = default
el zero d (x ∷ xs) = x
el (suc n) d (x ∷ xs) = el n d xs


elth : ∀ {X : Set} → (i : ℕ) → (d e : X) → (ls : List X) 
 → i < length ls → el i d ls ≡ e → e ∈ ls
elth i d e [] () prf
elth zero d e (.e ∷ ls) lss refl = here
elth (suc i) d e (x ∷ ls) lss prf = there (elth i d e ls (<-cong2 lss) prf)


alone : ∀ {X : Set} → (e : X) → (e' : X) → e ∈ (e' ∷ []) → e ≡ e'
alone .e' e' here = refl
alone e e' (there ())





subsetDec' : {X : Set} → (x : X) → (rs : List X) → (eqd : (x y : X) → x ≡ y ⊎ ¬ x ≡ y) → x ∈ rs ⊎ ¬ x ∈ rs
subsetDec' x [] eqd = inj₂ (λ  () )
subsetDec' x (x₁ ∷ rs) eqd with eqd x x₁ 
subsetDec' x (.x ∷ rs) eqd | inj₁ refl = inj₁ here
subsetDec' x (x₁ ∷ rs) eqd | inj₂ y with subsetDec' x rs eqd 
subsetDec' x (x₂ ∷ rs) eqd | inj₂ y | inj₁ x₁ = inj₁ (there x₁)
subsetDec' x (x₁ ∷ rs) eqd | inj₂ y₁ | inj₂ y = inj₂ (asd  x x₁ rs y₁ y)
  where
    asd : {X : Set} → (x y : X) → (ys : List X) → ¬ x ≡ y → ¬ x ∈ ys → ¬ x ∈ (y ∷ ys)
    asd x₂ .x₂ ys yeq tin here = yeq refl
    asd x₂ y₂ ys yeq tin (there xin) = tin xin


subsetDec'' : {X : Set} → (x : X) → (rs : List X) → (eqd : (x y : X) → x ≡ y ⊎ ¬ x ≡ y) → Dec (x ∈ rs)
subsetDec'' x rs eqd with subsetDec' x rs eqd 
subsetDec'' x rs eqd | inj₁ x₁ = yes x₁
subsetDec'' x rs eqd | inj₂ y = no y


open import Data.Bool
open import Utilities.Logic 

filter-nest : {X : Set} → (xs : List X)  
 → (p q : X → Bool)
 → filter p (filter q xs) ≡ filter (λ e → p e ∧ q e) xs
filter-nest [] p q = refl
filter-nest (x ∷ xs) p q with inspect  (q x) | inspect (p x)
filter-nest (x ∷ xs) p q | it true x₁ | it true g rewrite x₁ | g = cong (_∷_ x) (filter-nest xs p q)
filter-nest (x ∷ xs) p q | it true x₁ | it false g rewrite x₁ | g = filter-nest xs p q
filter-nest (x ∷ xs) p q | it false x₁ | it true g rewrite x₁ | g = filter-nest xs p q
filter-nest (x ∷ xs) p q | it false x₁ | it false g rewrite x₁ | g = filter-nest xs p q 

filter-id : {X : Set} → (xs : List X) → filter (λ e → true) xs ≡ xs
filter-id [] = refl
filter-id (x ∷ xs) = cong (_∷_ x) (filter-id xs)


filter-∈ : {X : Set} → (x : X) → (xs : List X) → (p : X → Bool) 
  → x ∈ filter p xs → x ∈ xs
filter-∈ x [] p ()
filter-∈ x (x₁ ∷ xs) p pin with p x₁
filter-∈ x₁ (.x₁ ∷ xs) p here | true = here
filter-∈ x (x₁ ∷ xs) p (there pin) | true = there (filter-∈ x xs p  pin)
filter-∈ x (x₁ ∷ xs) p pin | false = there (filter-∈ x xs p pin)


filter-el : {X : Set} → (x : X) → (xs : List X) 
  → (p : X → Bool)
  → x ∈ filter p xs → p x ≡ true
filter-el x [] p ()
filter-el x (x₁ ∷ xs) p xin with inspect (p x₁) 
filter-el x₂ (x₁ ∷ xs) p xin | it true x rewrite x with xin 
filter-el x₁ (.x₁ ∷ xs) p xin | it true x | here = x
filter-el x₂ (x₁ ∷ xs) p xin | it true x |  there xin' = filter-el x₂ xs p xin'
filter-el x₂ (x₁ ∷ xs) p xin | it false x rewrite x = filter-el x₂ xs p xin



filter-in2 : {X : Set} → (xs : List X) → ∀ x → (p : X → Bool) → x ∈ xs → p x ≡ true → x ∈ filter p xs
filter-in2 [] x p () px
filter-in2 (x ∷ xs) .x p here px rewrite px = here
filter-in2 (x ∷ xs) x₁ p (there xin) px with p x 
filter-in2 (x ∷ xs) x₁ p (there xin) px | true = there (filter-in2 xs x₁ p xin px)
filter-in2 (x ∷ xs) x₁ p (there xin) px | false = (filter-in2 xs x₁ p xin px)


emptDec : {X : Set} → (xs : List X) → Dec (xs ≡ [])
emptDec [] = yes refl
emptDec (x ∷ xs) = no (λ { () })



any-prop : {X : Set} → (p : X → Bool)
 → (ys₁ ys₂ xs₁ xs₂ : List X)
 → (x y : X)
 →  ys₁ ++ y ∷ ys₂ ≡ xs₁ ++ x ∷ xs₂
 → any p ys₁ ≡ false
 → any p xs₁ ≡ false
 → p y ≡ true
 → p x ≡ true
 → ys₁ ≡ xs₁
any-prop p [] ys2 [] xs2 x y pr anp1 refl py px = refl
any-prop p (x ∷ ys1) ys2 [] xs2 x₁ y pr anp1 refl py px with cong (λ { (z ∷ zs) → z ; [] → x  }) pr  
... | x=x1 rewrite x=x1 | px with anp1
... | ()
any-prop p [] ys2 (x ∷ xs1) xs2 x₁ y pr refl anyp py px with cong (λ { (z ∷ zs) → z ; [] → x  }) pr 
... | x=y rewrite x=y | py with anyp
... | ()
any-prop p (x ∷ ys1) ys2 (x₁ ∷ xs1) xs2 x₂ y pr anp1 anyp py px rewrite cong (λ { (z ∷ zs) → z ; [] → x  }) pr = cong (_∷_ x₁) (any-prop p ys1 ys2 xs1 xs2 x₂ y (cong (drop 1) pr) (any-h p ys1  x anp1) (any-h p xs1 x₁ anyp) py px)
  where
    any-h : {X : Set} → (p : X → Bool) → (xs : List X) → ∀ x → any p (x ∷ xs) ≡ false → any p xs ≡ false
    any-h p xs x pr with p x
    any-h p₁ xs x₃ () | true
    any-h p₁ xs x₃ pr₁ | false = pr₁




_SubSetOf_ : ∀ {A : Set} → List A → List A → Set
as₁ SubSetOf as₂ = ∀ {a} → a ∈ as₁ → a ∈ as₂


subset-dec : {X : Set}
  → Decidable (_≡_ {A = X})
  → Decidable (_SubSetOf_ {A = X}) 
subset-dec  eqd [] rs2 = yes (λ () )
subset-dec {_} eqd (x ∷ rs1) rs2 with eq2in eqd x rs2
subset-dec {X} eqd (x ∷ rs1) rs2 |  yes x₁ with subset-dec eqd rs1 rs2 
subset-dec {X} eqd (x₁ ∷ rs1) rs2 | yes x₂ | yes x = yes asd
  where
    asd : {a : X} → a ∈ (x₁ ∷ rs1) → a ∈ rs2
    asd here = x₂
    asd {a} (there ain) = x {a} ain
subset-dec {X} eqd (x ∷ rs1) rs2  | yes x₁ | no y = no (λ q → y (asd q))
  where
    asd : ({a : X} → a ∈ (x ∷ rs1) → a ∈ rs2) 
      → {a : X} → a ∈ rs1 → a ∈ rs2
    asd prop {a} ain = prop {a} (there ain)
subset-dec  {_} eqd (x ∷ rs1) rs2  | no y = no (λ q → y (q {x} here))



map-cong : {X Y : Set} → (f : X → Y) →  ∀ x xs → x ∈ xs → f x ∈ map f xs
map-cong f x ._ here = here
map-cong f x ._ (there xin) = there (map-cong f x _ xin)

map-pr1 : {X Y : Set} → (xs : List X)  → (f : X → Y) → (map proj₁ (map (λ x → x , f x) xs)) ≡ xs
map-pr1 [] f = refl
map-pr1 (x ∷ xs) f = cong (_∷_ x) (map-pr1 xs f)




map∃' : {X Y : Set}  → (a : Y) → (f : X → Y) 
 → (xs : List X)
 → a ∈ map f xs → Σ[ x ∈ X ] x ∈ xs × (f x) ≡ a
map∃' a f [] ()
map∃' .(f x) f (x ∷ xs) here = x , here , refl
map∃' a f (x ∷ xs) (there pr) with map∃' a f xs pr 
... | o1 , o2 , o3 = o1 , there o2 , o3


map∃ : {X Y : Set} → (_==_ : Decidable (_≡_ {A = Y})) → (a : Y) → (f : X → Y) 
 → (xs : List X)
 → a ∈ map f xs → Σ[ x ∈ X ] x ∈ xs × (f x) ≡ a
map∃ eq a f [] ()
map∃ eq a f (x ∷ xs) x₁ with eq (f x) a
map∃ eq a f (x ∷ xs) x₁ | yes p rewrite p = x , here , p
map∃ eq .(f x) f (x ∷ xs) here | no ¬p with ¬p refl 
... | ()
map∃ eq a f (x ∷ xs) (there x₁) | no ¬p with map∃ eq a f xs x₁ 
map∃ eq a f (x ∷ xs) (there x₁) | no ¬p | proj₁ , o1 , o2  = proj₁ , there o1 , o2


∈-eq-cong : {X : Set} → (x : X) → (xs ys : List X) →  x ∈ xs → xs ≡ ys → x ∈ ys
∈-eq-cong x xs .xs xsin refl = xsin



map-cong2 : {X Y : Set} → (f : Y → X) → (t : X → Y) 
  → (∀ x → t (f x) ≡ x)
  → ∀ x xs → f x ∈ map f xs → x ∈ xs
map-cong2 f t pr x [] ()
map-cong2 f t pr x (x₁ ∷ xs) pr2 with map-cong2' (f x) (f x₁) (map f xs) pr2
  where
     map-cong2' : {X : Set} → (x x1 : X) → (xs : List X) 
        → x ∈ (x1 ∷ xs) → x ≡ x1 ⊎ x ∈ xs
     map-cong2' x1 .x1 xs here = inj₁ refl
     map-cong2' x1 x2 xs (there inp) = inj₂ inp
map-cong2 f t pr x (x₁ ∷ xs) pr2 | inj₁ x₂ with cong t x₂
... | z rewrite pr x₁ | pr x = subst (λ h → h ∈ (x₁ ∷ xs)) (sym z) here
map-cong2 f t pr x (x₁ ∷ xs) pr2 | inj₂ y = there (map-cong2 f t pr _ _ y)


map-cong3 : {X Y : Set} → (f : Y → X)
  → (∀ x1 x2 → f x1 ≡ f x2 → x1 ≡ x2)
  → ∀ x xs → f x ∈ map f xs → x ∈ xs
map-cong3 f pr x xs xi with map∃'  (f x) f xs xi 
... | o1 , o2 , o3 rewrite pr o1 x o3 = o2




len-= : {X : Set} → (o1 o2 p1 p2 : List X) 
 → o1 ++ o2 ≡ p1 ++ p2 → length o1 ≡ length p1 → o1 ≡ p1
len-= [] o2 [] p2 pr len = refl
len-= [] o2 (x ∷ p1) p2 pr ()
len-= (x ∷ o1) o2 [] p2 pr ()
len-= (x ∷ o1) o2 (x₁ ∷ p1) p2 pr len rewrite len-= o1 o2 p1 p2 (cong (drop 1) pr) (cong pred len) | cong (λ { (z ∷ zs) → z ; [] → x }) pr = refl

len-=2 : {X : Set} → (o1 o2 p1 p2 : List X) 
 → o1 ++ o2 ≡ p1 ++ p2 → length o1 ≡ length p1 → o2 ≡ p2
len-=2 [] o2 [] p2 prf x = prf
len-=2 [] o2 (x ∷ p1) p2 prf ()
len-=2 (x ∷ o1) o2 [] p2 prf ()
len-=2 (x ∷ o1) o2 (x₁ ∷ p1) p2 prf x₂ = len-=2 o1 o2 p1 p2 (cong (drop 1) prf) (cong pred x₂)


list-⊥ : {X : Set} → (x : X) → (p1 p2 : List X) → p1 ≡ p1 ++ x ∷ p2 → ⊥
list-⊥ x [] p2 ()
list-⊥ x (x₁ ∷ p1) p2 pr = list-⊥ x p1 p2 (cong (drop 1) pr)

list-div : {X : Set} (a b : ℕ) → (xs : List X) 
  → a ≤ b → Σ[ xs' ∈ List X ] take b xs ≡ take a xs ++ xs'
list-div zero zero [] pr = [] , refl
list-div zero (suc b) [] pr = [] , refl
list-div (suc a) zero [] pr = [] , refl
list-div (suc a) (suc b) [] pr = [] , refl
list-div zero zero (x ∷ xs) pr = [] , refl
list-div zero (suc b) (x ∷ xs) pr = x ∷ take b xs , refl
list-div (suc a) zero (x ∷ xs) ()
list-div (suc a) (suc b) (x ∷ xs) (s≤s pr) with list-div a b xs pr 
... | o1 , o2 = o1 , cong (_∷_ x) o2

take-prop : {X : Set} → (o1 o2 : List X) → take (length o1) (o1 ++ o2) ≡ o1
take-prop [] o2 = refl
take-prop (x ∷ o1) o2 = cong (_∷_ x) (take-prop o1 o2)

++-[] : {X : Set} → (o1 : List X) → o1 ++ [] ≡ o1
++-[] [] = refl
++-[] (x ∷ o1) = cong (_∷_ x) (++-[] o1)



map-def : ∀ {a b} {A : Set a} → {B : A → Set b} → (A → Σ[ a ∈ A ] B a) → List A → List (Σ[ a ∈ A ] B a)
map-def f [] = []
map-def f (x ∷ l) = f x ∷ map-def f l

lft : ∀ {a} →  {X : Set a} → (xs : List X) → List (Σ[ x ∈ X ] x ∈ xs)
lft [] = []
lft (x ∷ xs) = (x , here) ∷ map (λ { (e , p) → e , there p }) (lft xs)


map-in : ∀ {a b} {A : Set a} → {B : Set b} → (as : List A) → (Σ[ a ∈ A ] a ∈ as → B) → List B
map-in xs f = map f (lft xs)


mapmap : ∀{a b c} {X : Set a}{Y : Set b}{Z : Set c} → (g : Y → Z) → (f : X → Y)
  → (xs : List X)
  → map g (map f xs) ≡  map (λ x → g (f x)) xs
mapmap f g [] = refl
mapmap f g (x ∷ xs) = cong (_∷_ _) (mapmap f g xs)

map-in-pr : ∀{a b} → {A : Set a} → {B : Set b} → (as : List A) → (f : Σ[ a ∈ A ] a ∈ as → B) → ∀ a → a ∈ as → Σ[ p ∈ (a ∈ as) ] (f (a , p)) ∈ (map-in as f)
map-in-pr [] f a₁ ()
map-in-pr (x ∷ as) f .x here = here , here
map-in-pr (x ∷ as) f x₁ (there ain) with map-in-pr as (λ a → f ((proj₁ a) , (there (proj₂ a)))) x₁ ain 
... | ass , ps rewrite mapmap f (λ ep → proj₁ ep , there (proj₂ ep))  (lft as) = there ass , there ps


map-def-pr : {l1 l2 : Level}{X : Set l1}{Y : X → Set l2} → (l : List X) 
  → (f : (x : X) → Y x)→ map proj₁ (map-def (λ el1 → el1 , f el1) l) ≡ l
map-def-pr [] f = refl
map-def-pr (x ∷ l) f = cong (_∷_ x) (map-def-pr l f)



NoDup+Dup : {X : Set} → (xs : List X) → Set
NoDup+Dup {X} xs = NoDup xs ⊎ (Σ[ ys ∈ List X ] 
                               Σ[ zs ∈ List X ] 
                               Σ[ x ∈ X ] xs ≡ ys ++ zs × x ∈ ys × x ∈ zs)



count : {X : Set} → DecEq X → X → List X → ℕ
count d x [] = 0
count d x₁ (x ∷ xs)  with d x x₁ 
... | yes _ = 1 + count d x₁ xs
... | no _  = count d x₁ xs


countHom : {X : Set} → (eq : DecEq X) → (xs ys : List X) → (x : X) 
  →  count eq x (xs ++ ys) ≡ count eq x xs + count eq x ys
countHom d [] ys x = refl
countHom d (x ∷ xs) ys x₁ with d x x₁
countHom d (x ∷ xs) ys x₁ | yes p rewrite countHom d xs ys x₁ = refl
countHom d (x ∷ xs) ys x₁ | no ¬p rewrite countHom d xs ys x₁ = refl 


count∉ : {X : Set} → (eq : DecEq X) → (xs : List X) → (x : X) 
   → ¬ x ∈ xs → count eq x xs ≡ 0
count∉ d [] x xnin = refl
count∉ d (x ∷ xs) x₁ xnin with d x x₁ 
count∉ d (x ∷ xs) .x xnin | yes refl with xnin here
... | ()
count∉ d (x ∷ xs) x₁ xnin | no _ = count∉ d xs x₁ (λ xin → xnin (there xin)) 


count∈ : {X : Set} → (eq : DecEq X) → (xs : List X) → (x : X) 
  → x ∈ xs → Σ[ n ∈ ℕ ] count eq x xs ≡ suc n
count∈ d (.x ∷ xs) x here with d x x 
... | yes p = count d x xs , refl
... | no p with p refl 
... | ()
count∈ d (y ∷ xs) x (there xin) with d y x 
... | yes p = count d x xs , refl
... | no p = count∈ d xs x xin


countNoDup : {X : Set} → (d : Decidable (_≡_ {A = X})) → (xs : List X) → (x : X) 
 → NoDup xs → x ∈ xs → count d x xs ≡ 1
countNoDup d xs x nd xin  with nd x  xin 
... | o1 , o2 , o3 , o4 , o5 rewrite o3 | countHom d o1 (x ∷ o2) x with d x x
... | yes p rewrite count∉ d  o1 x  o4 | count∉ d  o2 x  o5 = refl
... | no p with p refl 
... | ()

open import Utilities.NatProperties
notNoDup : {X : Set} → {d : DecEq X} → (xs : List X) 
  → (Σ[ ys ∈ List X ] 
      Σ[ zs ∈ List X ] 
      Σ[ x ∈ X ] xs ≡ ys ++ zs × (x ∈ ys) × (x ∈ zs)) 
  → ¬ NoDup xs
notNoDup {_} {d} xs (proj₁ , proj₂ , proj₃ , proj₄ , proj₅ , proj₆) nd 
  with nd proj₃ (subst (λ z → proj₃ ∈ z) (sym proj₄) (∈-weak-lft {_} {proj₁} {proj₂} {proj₃} proj₆)) 
... | o1 , o2 , o3 , o4 , o5  rewrite proj₄ with cong (count d proj₃) o3 
... | po rewrite countHom d proj₁ proj₂ proj₃ | countHom d o1 (proj₃ ∷ o2) proj₃  with d proj₃ proj₃ 
... | no p = p refl
... | yes p rewrite count∉ d o1 proj₃ o4 | count∉ d o2 proj₃ o5 with 
 count∈ d proj₁ proj₃ proj₅ | count∈ d proj₂ proj₃ proj₆
... | z , zp | w , wp  rewrite zp | wp | +-com z (suc w) with po 
... | () 


nodup+dup : {X : Set} → DecEq X → (xs : List X) → NoDup+Dup xs
nodup+dup dec [] = inj₁ (λ { x () })
nodup+dup dec (x ∷ xs)  with nodup+dup dec xs  
nodup+dup dec (x₁ ∷ xs) | inj₁ x with (eq2in dec) x₁ xs 
nodup+dup dec (x₁ ∷ xs) | inj₁ x | yes p with ∃-split x₁ xs p 
... | o1 , o2 , o3 = inj₂ (x₁ ∷ o1 , x₁ ∷ o2 , x₁ , cong (_∷_ x₁) o3 , here , here) 
nodup+dup {X} dec (x₁ ∷ xs) | inj₁ x | no ¬p = inj₁ (h xs x₁ ¬p x)
  where
    h : (xs1 : List X) → (x₁ : X) → (¬p  : ¬ x₁ ∈ xs1) 
      → NoDup xs1
      → (x₂ : X)
      → x₂ ∈ (x₁ ∷ xs1) →
      Σ (List X)
      (λ ys →
         Σ (List X)
         (λ zs →
            Σ (x₁ ∷ xs1 ≡ ys ++ x₂ ∷ zs)
            (λ x₃ → Σ (x₂ ∈ ys → ⊥) (λ x₄ → x₂ ∈ zs → ⊥))))
    h xs₁ x1 ¬p nd x xin with dec x x1
    h xs₁ x1 ¬p₁ nd .x1 here | yes refl = [] , xs₁ , refl , (λ { () }) , ¬p₁
    h xs₁ x1 ¬p₁ nd .x1 (there xin) | yes refl with ¬p₁ xin 
    ... | ()
    h xs₁ x1 ¬p₂ nd .x1 here | no ¬p₁ with ¬p₁ refl 
    ... | ()

    h xs₁ x1 ¬p₂ nd x₂ (there xin) | no ¬p₁ with nd x₂ xin 
    ... | q1 , q2 , q3 , q4 , q5 = x1 ∷ q1 , q2 , cong (_∷_ x1) q3 , blh x₂ x1 q1 ¬p₁ q4 , q5
      where
        blh : {A : Set} → (a b : A) → (cs : List A) →  (a ≡ b → ⊥) → (a ∈ cs → ⊥) → a ∈ (b ∷ cs) → ⊥
        blh a .a cs pr1 pr2 here = pr1 refl
        blh a b cs pr1 pr2 (there pr3) = pr2 pr3
nodup+dup dec (x₁ ∷ xs)  | inj₂ (ys , zs , e , p , q1 , q2) = inj₂ (x₁ ∷ ys , zs , e , cong (_∷_ x₁) p , there q1 , q2) 



nodupDec2 : {X : Set} → DecEq X → (xs : List X) → Dec (NoDupInd xs)
nodupDec2 eq [] = yes end
nodupDec2 eq (x ∷ xs) with nodupDec2 eq xs 
nodupDec2 eq (x ∷ xs) | yes p with eq2in eq x xs 
nodupDec2 eq (x ∷ xs) | yes p₁ | yes p = no (λ { (x₁ ::: nd) → x₁ p })
nodupDec2 eq (x ∷ xs) | yes p | no ¬p = yes (¬p ::: p)
nodupDec2 eq (x ∷ xs) | no ¬p = no (λ { (x₁ ::: nd) → ¬p nd } )

nodupDec : {X : Set} → DecEq X → (xs : List X) → Dec (NoDup xs)
nodupDec d xs with nodup+dup d xs
nodupDec d xs | inj₁ x = yes x
nodupDec d xs | inj₂ y = no (notNoDup {_} {d} xs y)
