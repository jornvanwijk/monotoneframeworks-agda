open import Data.Nat
open import Relation.Binary
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple 
module Util.Nat where


>⇒≠ : _>_ ⇒ _≢_ 
>⇒≠ (s≤s x) refl = 1+n≰n x

>⇒≥ : _>_ ⇒ _≥_ 
>⇒≥ (s≤s x) = ≤-step x 

<⇒≠ : _<_ ⇒ _≢_ 
<⇒≠ (s≤s x) refl = 1+n≰n x

open import Data.Product
open import Relation.Nullary.Negation
open import Data.Empty
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans; antisym to ≤-antisym; refl to ≤-refl)
≤∧≠⇒< : ∀{a b} → a ≤ b → a ≢ b → a < b 
≤∧≠⇒< {a} {b} x x₁ with StrictTotalOrder.compare strictTotalOrder a b
≤∧≠⇒< {a} {b} x x₁ | tri< a₁ ¬b ¬c = a₁
≤∧≠⇒< {a} {b} x x₁ | tri≈ ¬a b₁ ¬c = contradiction b₁ x₁
≤∧≠⇒< {a} {b} x x₁ | tri> ¬a ¬b c = ⊥-elim (¬a (⊥-elim (x₁ (≤-antisym x (≤-trans (≤-step ≤-refl) c)))))

≮⇒≥ : _≮_ ⇒ _≥_ 
≮⇒≥ {a} {b} x with StrictTotalOrder.compare strictTotalOrder a b
≮⇒≥ {i} {j} x | tri< a ¬b ¬c = ⊥-elim (¬b (⊥-elim (x a)))
≮⇒≥ {i} {.i} x | tri≈ ¬a refl ¬c = ≤-refl
≮⇒≥ {i} {j} x | tri> ¬a ¬b c = ≤-trans (≤-step ≤-refl) c


cancel-+-right : ∀ i {j k} → j + i ≡ k + i → j ≡ k
cancel-+-right i {j} {k} x = cancel-+-left i (trans (+-comm i j) (trans x (+-comm k i)))

<-+-right : ∀ a b c → a < b → a < b + c
<-+-right a b c x = subst (λ r → a < r) (+-comm c b) (≤-steps c x)

+-suc′ : ∀ m n → suc m + n ≡ suc (m + n)
+-suc′ m n = trans (sym (+-suc m n)) (+-suc m n) 

m≤n⇒m≤n+k : {m n : ℕ} → m ≤ n → (k : ℕ) → m ≤ n + k
m≤n⇒m≤n+k {zero} {n} m≤n k = z≤n
m≤n⇒m≤n+k {suc m} {zero} () k 
m≤n⇒m≤n+k {suc m} {suc n} (s≤s m≤n) k = s≤s (m≤n⇒m≤n+k m≤n k)

m≤n⇒m≤k+n : {m n : ℕ} → m ≤ n → (k : ℕ) → m ≤ k + n
m≤n⇒m≤k+n {m} {n} m≤n k = subst (λ y → m ≤ y) (+-comm n k) (m≤n⇒m≤n+k m≤n k)

m+n≤m⇒n≡0 : {m n : ℕ} → m + n ≤ m → n ≡ 0
m+n≤m⇒n≡0 {zero} {.0} z≤n = refl
m+n≤m⇒n≡0 {suc m} {n} (s≤s x) = m+n≤m⇒n≡0 x

m+n≤n⇒m≡0 : {m n : ℕ} → m + n ≤ n → m ≡ 0
m+n≤n⇒m≡0 {m} {n} x = m+n≤m⇒n≡0 (subst (λ y → y ≤ n) (+-comm m n) x)

m+n≡0⇒m≡0 : {m n : ℕ} → m + n ≡ 0 → m ≡ 0
m+n≡0⇒m≡0 {m} {zero} x = trans (sym (+-right-identity m)) x
m+n≡0⇒m≡0 {zero} {suc n} x = refl
m+n≡0⇒m≡0 {suc m} {suc n} ()

a+b≡c⇒a≤c : {a b c : ℕ} → a + b ≡ c → a ≤ c
a+b≡c⇒a≤c {a} {b} {.(a + b)} refl = m≤m+n a b

a+b≤c⇒a≤c : {a b c : ℕ} → a + b ≤ c → a ≤ c
a+b≤c⇒a≤c {zero} {b} {c} x = z≤n
a+b≤c⇒a≤c {suc a} {b} {zero} ()
a+b≤c⇒a≤c {suc a} {b} {suc c} (s≤s x) = s≤s (a+b≤c⇒a≤c x)

a+b≤c⇒b≤c : {a b c : ℕ} → a + b ≤ c → b ≤ c
a+b≤c⇒b≤c {a} {b} {c} a+b≤c = a+b≤c⇒a≤c (subst (λ y → y ≤ c) (+-comm a b) a+b≤c)



open import Data.Empty
open import Data.Sum
open import Relation.Nullary
atomic : (a : ℕ) → ¬ (Σ[ n ∈ ℕ ] a < n × n < suc a)
atomic zero (zero , () , s≤s z≤n)
atomic (suc a) (zero , () , proj₅)
atomic zero (suc proj₃ , proj₄ , s≤s ())
atomic (suc a) (suc proj₃ , proj₄ , proj₅) = atomic a (proj₃ , ≤-pred proj₄ , ≤-pred proj₅)


suc⁻¹ : (a b : ℕ) → suc a ≡ suc b → a ≡ b
suc⁻¹ zero .0 refl = refl
suc⁻¹ (suc a) zero ()
suc⁻¹ (suc a) (suc .a) refl = refl


a∸b+b≡a : (a b : ℕ) → b ≤ a → (a ∸ b) + b ≡ a
a∸b+b≡a a zero x = +-right-identity a
a∸b+b≡a zero (suc b) ()
a∸b+b≡a (suc a) (suc b) (s≤s x) = trans (+-suc (a ∸ b) b) (cong suc (a∸b+b≡a a b x))
