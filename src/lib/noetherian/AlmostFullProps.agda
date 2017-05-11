
module AlmostFullProps where


open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Data.List
open import Utilities
open import Coinduction
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Sum renaming (_⊎_ to _+_) hiding (map)
open import Data.Empty
open import Function


open import Noetherian
open import AlmostFull

data  MemR {X : Set}(R : X → X → Set) (x : X) : List X → Set where
  here  : ∀ {y xs} → R y x → MemR R x (y ∷ xs)
  there : ∀ {y xs} → MemR R x xs → MemR R x (y ∷ xs)

data DupR {X : Set}(R : X → X → Set) : List X → Set where
  duphere  : ∀ {x xs} → MemR R x xs → DupR R (x ∷ xs)
  dupthere : ∀ {x xs} → DupR R xs → DupR R (x ∷ xs)

data NoethAccR' (X : Set)(R : X → X → Set) (xs : List X) : Set where
  base : DupR R xs → NoethAccR' X R xs
  step : (∀ x → NoethAccR' X R (x ∷ xs)) → NoethAccR' X R xs

NoethAccR : (X : Set)(R : X → X → Set) → Set
NoethAccR X R = NoethAccR' X R []

R+ : {X : Set}(R : X → X → Set)(xs : List X) → X → X → Set
R+ R [] = R
R+ R (x ∷ xs) y z = R+ R xs y z + R+ R xs x y

liftR+ : {X : Set}(R : X → X → Set)(xs : List X) →
         ∀{x y} → R x y → R+ R xs x y
liftR+ R [] r = r
liftR+ R (x ∷ xs) r = inj₁ (liftR+ R xs r)        

MemR+ : {X : Set}{R : X → X → Set}
        {xs : List X}{x : X} → MemR R x xs →
        ∀ y z → R+ R (x ∷ xs) y z
MemR+ {xs = _ ∷ xs} (here m) y z = inj₂ (inj₂ (liftR+ _ xs m))
MemR+ (there m) y z with MemR+ m y z
MemR+ (there m) y z | inj₁ r = inj₁ (inj₁ r)
MemR+ (there m) y z | inj₂ r = inj₂ (inj₁ r)        

DupR+ : {X : Set}{R : X → X → Set}
        {xs : List X} → DupR R xs →
        ∀ x y → R+ R xs x y
DupR+ (duphere m) = MemR+ m
DupR+ (dupthere d) x y = inj₁ (DupR+ d x y)

NoethAccR'→AF : {X : Set}{R : X → X → Set}
             (xs : List X) → NoethAccR' X R xs → AF X (R+ R xs)
NoethAccR'→AF xs (base d) = afzt (DupR+ d)
NoethAccR'→AF xs (step n) = afsup (λ x → NoethAccR'→AF (x ∷ xs) (n x))

NoethAccR→AF : {X : Set}{R : X → X → Set} → NoethAccR X R → AF X R
NoethAccR→AF n = NoethAccR'→AF [] n            

∈→Mem≡ : ∀{X}{xs : List X}{x} → x ∈ xs → MemR _≡_ x xs
∈→Mem≡ (here refl) = here refl
∈→Mem≡ (there m) = there (∈→Mem≡ m)

Dup→Dup≡ : ∀{X}{xs : List X} → Dup xs → DupR _≡_ xs
Dup→Dup≡ (duphere m) = duphere (∈→Mem≡ m)
Dup→Dup≡ (dupthere d) = dupthere (Dup→Dup≡ d)

NoethAcc'→NoethAcc≡' : {X : Set}(xs : List X) →
               NoethAcc' X xs → NoethAccR' X _≡_ xs
NoethAcc'→NoethAcc≡' xs (stop d) = base (Dup→Dup≡ d)
NoethAcc'→NoethAcc≡' xs (ask n) = step (λ x → NoethAcc'→NoethAcc≡' (x ∷ xs) (n x))

NoethAcc→NoethAcc≡ : {X : Set} → NoethAcc X → NoethAccR X _≡_
NoethAcc→NoethAcc≡ n = NoethAcc'→NoethAcc≡' [] n


NoethAcc→AFEq : {X : Set} → NoethAcc X → AFEq X
NoethAcc→AFEq n = NoethAccR→AF (NoethAcc→NoethAcc≡ n)

DupR+2 : {X : Set}{R : X → X → Set}(xs : List X) →
         ∀{x y} → R+ R xs x y → DupR R (y ∷ x ∷ xs)
DupR+2 [] p = duphere (here p)
DupR+2 (x' ∷ xs) (inj₁ p) with DupR+2 xs p
DupR+2 (x' ∷ xs) (inj₁ p) | duphere (here r) = duphere (here r)
DupR+2 (x' ∷ xs) (inj₁ p) | duphere (there m) = duphere (there (there m))
DupR+2 (x' ∷ xs) (inj₁ p) | dupthere (duphere m) = dupthere (duphere (there m))
DupR+2 (x' ∷ xs) (inj₁ p) | dupthere (dupthere d) = dupthere (dupthere (dupthere d))
DupR+2 (x' ∷ xs) (inj₂ p) with DupR+2 xs p
DupR+2 (x' ∷ xs) (inj₂ p) | duphere (here r) = dupthere (duphere (here r))
DupR+2 (x' ∷ xs) (inj₂ p) | duphere (there m) = dupthere (duphere (there m))
DupR+2 (x' ∷ xs) (inj₂ p) | dupthere (duphere m) = dupthere (dupthere (duphere m))
DupR+2 (x' ∷ xs) (inj₂ p) | dupthere (dupthere d) = dupthere (dupthere (dupthere d))

AF→NoethAccR' : {X : Set}{R : X → X → Set}(xs : List X) →
             AF X (R+ R xs) → NoethAccR' X R xs
AF→NoethAccR' xs (afzt p) = step (λ x → step (λ y → base (DupR+2 xs (p x y))))
AF→NoethAccR' xs (afsup p) = step (λ x → AF→NoethAccR' (x ∷ xs) (p x))

AF→NoethAccR : {X : Set}{R : X → X → Set} → AF X R → NoethAccR X R
AF→NoethAccR a = AF→NoethAccR' [] a

Mem≡→∈ : ∀{X}{xs : List X}{x} → MemR _≡_ x xs → x ∈ xs
Mem≡→∈ (here refl) = here refl
Mem≡→∈ (there m) = there (Mem≡→∈ m)

Dup≡→Dup : ∀{X}{xs : List X} → DupR _≡_ xs → Dup xs
Dup≡→Dup (duphere m) = duphere (Mem≡→∈ m)
Dup≡→Dup (dupthere d) = dupthere (Dup≡→Dup d)

NoethAcc≡'→NoethAcc' : {X : Set}(xs : List X) →
               NoethAccR' X _≡_ xs → NoethAcc' X xs
NoethAcc≡'→NoethAcc' xs (base d) = stop (Dup≡→Dup d)
NoethAcc≡'→NoethAcc' xs (step n) = ask (λ x → NoethAcc≡'→NoethAcc' (x ∷ xs) (n x))

NoethAcc≡→NoethAcc : {X : Set} → NoethAccR X _≡_ → NoethAcc X 
NoethAcc≡→NoethAcc n = NoethAcc≡'→NoethAcc' [] n


AFEq→NoethAcc : {X : Set} → AFEq X → NoethAcc X
AFEq→NoethAcc a = NoethAcc≡→NoethAcc (AF→NoethAccR a)


