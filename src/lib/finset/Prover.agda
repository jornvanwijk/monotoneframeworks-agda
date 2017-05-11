
module Prover where

open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary
open import Relation.Unary as U using (Pred)

open import Level

open import Data.List
open import Data.Product hiding (map)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat hiding (_⊔_)

open import Utilities.ListProperties 
open import Utilities.Logic 

open import Finiteness

for-all-constl : ∀ {a b c} 
   → {X : Set} {P : X → Set a}
   → {Q : Σ[ x ∈ X ] P x → Set b}
   → {Z : Σ[ x ∈ X ] P x → Set c}
   → (ps : List (Σ[ x ∈ X ] P x))
   → U.Decidable Z
   → (∀ p → Z p → Dec (Q p))
   → Dec (∀ p → p ∈ ps → Z p → Q p)
for-all-constl [] d pr = yes (λ { _ () } )
for-all-constl (x ∷ p) d pr with for-all-constl p d pr  | d x
for-all-constl {X = X} {P = P} {Q = Q} (x ∷ p) d pr 
  | yes p₁ | yes p₂ with pr x  p₂ 
for-all-constl {X = X} {P = P} {Q = Q} {Z = Z} (x ∷ p₁) d pr 
  | yes p₃ | yes p₂ | yes p 
 = yes (hlp x p)
  where 
   hlp : (x : Σ X P) → (Q x) →  (p₄ : Σ X P) → p₄ ∈ (x ∷ p₁) → Z p₄ → Q p₄ 
   hlp x₁ zx .x₁ here zp = zx
   hlp x₁ zx x₂ (there p4i) zp = p₃ x₂ p4i zp
  
for-all-constl {X = X} {P = P} {Q = Q} {Z = Z} (x ∷ p) d pr 
  | yes p₁ | yes p₂ | no ¬p = no hlp
   where
    hlp : ¬ ((p₃ : Σ X P) → p₃ ∈ (x ∷ p) → Z p₃ → Q p₃)
    hlp pr' = ¬p (pr' x  here p₂)

for-all-constl {X = X} {P = P} {Q = Q} {Z = Z} (x ∷ p) d pr 
  | yes p₁ | no ¬p = yes (hlp x ¬p)
   where
    hlp : (x : Σ X P) → ¬ Z x → (p₂ : Σ X P) → p₂ ∈ (x ∷ p) → Z p₂ → Q p₂
    hlp x₁ nz .x₁ here zp with nz zp
    ... | ()
    hlp x₁ nz x₂ (there pi) zp = p₁ x₂ pi zp

for-all-constl {X = X} {P = P} {Q = Q} {Z = Z} (x ∷ p) d pr | no ¬p  | z 
  = no (λ pq → ¬p (λ zz zzi zzz → pq  zz (there zzi) zzz))


for-all-constl' : ∀ {a b c d} 
   → {X : Set d} {P : X → Set a}
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (ps : List X)
   → (∀ p → p ∈ ps → P p)
   → U.Decidable Z
   → (∀ x → P x → Z x → Dec (Q x))
   →  Dec (∀ x → x ∈ ps → Z x → P x → Q x)
for-all-constl' [] pr zd qd = yes (λ { _ () })
for-all-constl' (x ∷ ps) pr zd qd 
  with for-all-constl' ps (λ p pi → pr p (there pi)) zd qd 
for-all-constl' (x ∷ ps) pr zd qd | yes p with zd x 
for-all-constl' (x ∷ ps) pr zd qd | yes p₁ | yes p 
  with qd x (pr x here) p 
for-all-constl' {X = X}{P = P}{Q = Q}{Z = Z} (x ∷ ps) pr zd qd | yes p₂ 
  | yes p | yes p₁ = yes (hlp x p₁)
  where
   hlp : (x : X) → Q x → (x₁ : X) → x₁ ∈ (x ∷ ps) → Z x₁ → P x₁ → Q x₁
   hlp x₁ qx .x₁ here zx px = qx
   hlp x₁ qx x₂ (there xi) zx px = p₂ x₂  xi zx px

for-all-constl' {X = X}{P = P}{Q = Q}{Z = Z} (x ∷ ps) pr zd qd | yes p₁ | yes p 
  | no ¬p = no (λ pr' → ¬p (pr' x here p (pr x here)))

for-all-constl' {X = X}{P = P}{Q = Q}{Z = Z} (x ∷ ps) pr zd qd 
  | yes p | no ¬p = yes (hlp x ¬p)
  where
   hlp : (x : X) → ¬ Z x → (x₁ : X) → x₁ ∈ (x ∷ ps) → Z x₁ → P x₁ → Q x₁
   hlp x' zx' .x' here zx px with zx' zx 
   ... | ()
   hlp x' zx' x₁ (there xi) zx px = p x₁  xi zx px
for-all-constl' {X = X}{P = P}{Q = Q}{Z = Z}  (x ∷ ps) pr zd qd | no ¬p = no hlp
  where
   hlp : ¬ ((x₁ : X) → x₁ ∈ (x ∷ ps) → Z x₁ → P x₁ → Q x₁)
   hlp pr'' = ¬p (λ x1 x1i zx px → pr'' x1 (there x1i) zx px)


for-all-const : ∀ {a b c d} 
   → {X : Set d} 
   → {P : X → Set a}
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (kf : ListableSubset X P)
   → U.Decidable Z
   → (∀ x → P x → Z x → Dec (Q x))
   → Dec (∀ x → P x → Z x → Q x)
for-all-const {X = X}{P = P}{Q = Q}{Z = Z} (els , s , c) zd pr 
  with for-all-constl' els s zd  pr 
for-all-const (els , s , c₁) zd pr | yes p 
  = yes (λ x px zx → p x (c₁ x px) zx px)
for-all-const (els , s , c₁) zd pr | no ¬p 
  = no (λ pr' → ¬p (λ x xi zx px → pr' x px zx))


for-all :  {X : Set} {P : X → Set}{Q : X → Set}
             → (kf : ListableSubset X P)
             → (∀ x → {p : P x} → Dec (Q x))
             →  Dec (∀ x → {p : P x} → Q x)
for-all lsbl pr1 with for-all-const {Z = λ _  → ⊤} lsbl 
  (λ x → yes tt) (λ x px _ → pr1 x {px}) 
for-all lsbl pr1 | yes p = yes (λ x {px} → p x px tt)
for-all lsbl pr1 | no ¬p = no (λ pr → ¬p (λ x px _ → pr x {px}))

syntax for-all kf (λ x → z) = Π' x ∈ kf ∙ z


exists-constl' : ∀ {a b c d} 
   → {X : Set d} {P : X → Set a}
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (ps : List X)
   → (∀ p → p ∈ ps → P p)
   → U.Decidable Z
   → (∀ x → P x → Z x → Dec (Q x))
   →  Dec (Σ[ x ∈ X ] x ∈ ps × Z x × P x × Q x)
exists-constl' [] pi zd qd = no (λ { (a , () , c , d)  })
exists-constl' (x ∷ ps) pi zd qd with zd x 
exists-constl' (x ∷ ps) pi zd qd | yes p with qd x (pi x here)  p 
exists-constl' (x ∷ ps) pi zd qd | yes p | yes p₁ 
 = yes (x , here , p , pi x here , p₁) 
exists-constl' (x ∷ ps) pi zd qd | yes p | no ¬p 
  with exists-constl' ps (λ p pi' → pi p (there pi')) zd qd 
exists-constl' (x ∷ ps) pi zd qd | yes p | no ¬p 
  | yes (e1 , e2 , e3 , e4 , e5) = yes (e1 , there e2 , e3 , e4 , e5)
exists-constl' {X = X}{P = P}{Q = Q}{Z = Z} (x ∷ ps) pi zd qd 
  | yes p | no ¬p | no ¬p₁ = no hlp
  where
   hlp : ¬ (Σ[ y ∈ X ] (y ∈ (x ∷ ps) × Z y × P y × Q y))
   hlp (.x , here , zy , py , qy) = ¬p qy
   hlp (x₁ , there yi , zy , py , qy) = ¬p₁ (x₁ , yi , zy , py , qy)

exists-constl' (x ∷ ps) pi zd qd | no ¬p 
  with exists-constl' ps (λ p pi' → pi p (there pi')) zd qd 
exists-constl' (x ∷ ps) pi zd qd | no ¬p 
  | yes (e1 , e2 , e3 , e4 , e5)
  = yes (e1 , there e2 , e3 , e4 , e5)
exists-constl' {X = X}{P = P}{Q = Q}{Z = Z} (x ∷ ps) pi zd qd 
  | no ¬p₁ | no ¬p = no hlp
    where
     hlp : ¬ (Σ[ y ∈ X ] (y ∈ (x ∷ ps) × Z y × P y × Q y))
     hlp (.x , here , zy , py , qy) = ¬p₁ zy
     hlp (x₁ , there yi , zy , py , qy) = ¬p (x₁ , yi , zy , py , qy)


exists-const : ∀ {a b c d} 
   → {X : Set d} 
   → {P : X → Set a}
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (kf : ListableSubset X P)
   → U.Decidable Z
   → (∀ x → P x → Z x → Dec (Q x))
   → Dec (Σ[ x ∈ X ] P x × Z x × Q x)
exists-const (xs , s , c) zd pr with exists-constl' xs s zd pr 
exists-const (xs , s , c₁) zd pr | yes (x , xps , zx , px , qx) 
  = yes (x , px , zx , qx) 
exists-const (xs , s , c₁) zd pr | no ¬p 
  = no (λ { (x , zx , px , qx) → ¬p (x , c₁ x zx , px , zx , qx) })


exists :  {X : Set} {P : X → Set}{Q : X → Set}
             → (kf : ListableSubset X P)
             → (∀ x → P x → Dec (Q x))
             → Dec (Σ[ x ∈ X ] P x × Q x)
exists lsbl pr with exists-const {Z = λ _ → ⊤} lsbl 
  (λ _ → yes tt) (λ x px _ → pr x px) 
exists lsbl pr | yes (x , px , _ , z) = yes (x , px , z)
exists lsbl pr | no ¬p = no (λ {(z1 , z2 , z3) → ¬p (z1 , z2 , tt , z3) })



exists-const-lstbl : ∀ {b c d} 
   → {X : Set d} 
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (kf : Listable X)
   → U.Decidable Z
   → (∀ x → Z x → Dec (Q x))
   → Dec (Σ[ x ∈ X ] Z x × Q x)
exists-const-lstbl ls dz  dq 
  with exists-const (lstbl2subset ls) dz (λ x _ zx → dq x zx) 
exists-const-lstbl ls dz dq | yes (x , _ , zx , qx) 
  = yes (x , zx , qx)
exists-const-lstbl ls dz dq | no ¬p 
  = no (λ { (x , zx , qx) → ¬p (x , tt , zx , qx) })


exists-lstbl : ∀ {b d} 
   → {X : Set d} 
   → {Q : X → Set b}
   → (kf : Listable X)
   → (∀ x → Dec (Q x))
   → Dec (Σ[ x ∈ X ] Q x)
exists-lstbl kf pr 
  with exists-const-lstbl {Z = λ _ → ⊤} kf (λ _ → yes tt)  (λ x _ → pr x) 
... | yes (x , _ , qx) = yes (x , qx)
... | no ¬p = no (λ { (x1 , x2) → ¬p (x1 , tt , x2) })



forall-const-lstbl : ∀ {b c d} 
   → {X : Set d} 
   → {Q : X → Set b}
   → {Z : X → Set c}
   → (kf : Listable X)
   → U.Decidable Z
   → (∀ x → Z x → Dec (Q x))
   → Dec (∀ x → Z x  →  Q x)
forall-const-lstbl lstbl dz dq 
  with for-all-const (lstbl2subset lstbl) dz (λ x _ zx → dq x zx) 
forall-const-lstbl lstbl dz dq | yes p = yes (λ x zx → p x tt zx)
forall-const-lstbl lstbl dz dq | no ¬p = no (λ c → ¬p (λ x _ zx → c x zx))



forall-lstbl : ∀ {b d} 
   → {X : Set d} 
   → {Q : X → Set b}
   → (kf : Listable X)
   → (∀ x → Dec (Q x))
   → Dec (∀ x → Q x)
forall-lstbl kf dq 
  with forall-const-lstbl {Z = λ _ → ⊤} kf (λ _ → yes tt) (λ x _ → dq x) 
forall-lstbl kf dq | yes p = yes (λ x → p x tt)
forall-lstbl kf dq | no ¬p = no (λ pr → ¬p (λ x _ → pr x))



syntax forall-lstbl kf (λ x → z) = Π x ∈ kf ∙ z
syntax exists-lstbl kf (λ x → z) = ∃ x ∈ kf ∙ z



