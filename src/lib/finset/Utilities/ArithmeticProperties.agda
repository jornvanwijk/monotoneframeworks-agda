
module Utilities.ArithmeticProperties where

open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.Nat hiding (_<_)
open import Data.Empty
open import Data.Bool

data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

-- _+_ PROPERTIES
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc n) b c = cong suc (+-assoc n b c )

arth-lem1 : (n m : ℕ) → n + (suc m) ≡ suc (n + m)
arth-lem1 zero m = refl
arth-lem1 (suc n) m = cong suc (arth-lem1 n m)

+-comm : ∀ n m → (n + m) ≡ (m + n)
+-comm zero zero = refl
+-comm zero (suc n) = cong suc (+-comm zero n) 
+-comm (suc n) m rewrite +-comm n m = sym (arth-lem1 m n)

+-comm-sum : ∀ {a b c} → a + b ≡ c → b + a ≡ c
+-comm-sum {a} {b} {c} eq rewrite +-comm a b = eq

+-sym-lem : (c : ℕ) → c + 0 ≡ c
+-sym-lem zero = refl
+-sym-lem (suc c) = cong suc (+-sym-lem c) 


-- _<_ PROPERTIES
<-weak : ∀ a b  → (suc a) < b → a < b
<-weak n .(suc (suc n)) <-base     = <-step <-base
<-weak n .(suc n') (<-step {n'} y) = <-step (<-weak n n' y)

<-lemm1 : ∀ a b → b < suc (a + b)
<-lemm1 zero n' = <-base
<-lemm1 (suc n) zero = <-step (<-lemm1 n zero)
<-lemm1 (suc n) (suc n') = <-step (<-lemm1 n (suc n'))

<-0suc : ∀ n → 0 < suc n 
<-0suc zero = <-base
<-0suc (suc n) = <-step (<-0suc n)

<-cong1 : ∀ {k n} → k < n → suc k < suc n
<-cong1 {k} .{(suc k)} <-base = <-base
<-cong1 {k} .{(suc n)} (<-step {n} y) = <-step (<-cong1 y)

<-cong2 : ∀ {k n} → suc k < suc n → k < n
<-cong2 {k} .{(suc k)} <-base = <-base
<-cong2 {zero} {zero} (<-step ())
<-cong2 {zero} {(suc .1)} (<-step <-base) = <-step <-base
<-cong2 {zero} {(suc n)} (<-step (<-step y)) = <-step (<-cong2  (<-step y))
<-cong2 {(suc n)} {zero} (<-step ())
<-cong2 {(suc n)} {(suc .(suc (suc n)))} (<-step <-base) = <-step (<-base)
<-cong2 {(suc n)} {(suc n')} (<-step (<-step y)) = <-step (<-cong2 (<-step y)) 

<-lemm3 : ∀ {a b n} →  (suc a) + (suc b) ≡ (suc n) → (suc a) < (suc n)
<-lemm3 {zero} {b} eq  rewrite (sym eq) = <-cong1 (<-0suc b)
<-lemm3 {suc a} {b} {n} eq 
  rewrite (sym eq) 
  | +-comm (suc (suc a)) (suc b)  
  = <-lemm1 b (suc (suc a)) 

<-lemm2 : ∀ {a b n} →  (suc a) + (suc b) ≡ (suc n) → (suc b) < (suc n)
<-lemm2 {a} {b} {n} eq rewrite (+-comm (suc a) (suc b))
 = <-lemm3 eq



-- MINUS PROPERTIES
∸-lemm1 : (n k : ℕ) → k < (suc n) → (suc n) ∸ k ≡ suc (n ∸ k)
∸-lemm1 zero .0 <-base = refl
∸-lemm1 (suc n) .(suc n) <-base = ∸-lemm1 n n <-base
∸-lemm1 zero k (<-step ())
∸-lemm1 (suc n) zero (<-step y) = refl
∸-lemm1 (suc n) (suc n') (<-step y) = ∸-lemm1 n n' (<-weak _ _ y)

k∸k≡0 : (k : ℕ) → k ∸ k ≡ 0
k∸k≡0 zero = refl
k∸k≡0 (suc n) = k∸k≡0 n

∸-lemm2 : ∀ n k → (n + k) ∸ k ≡ n
∸-lemm2 zero k = k∸k≡0 k
∸-lemm2 (suc n) zero = cong suc (+-comm n 0)
∸-lemm2 (suc n) (suc n') rewrite arth-lem1 n n' with ∸-lemm1 (n + n') n' (<-lemm1 n n')
... | prf rewrite prf =   cong suc (∸-lemm2 n n')

∸-lemm3 : ∀ {n k} → (k < n) → n ∸ (n ∸ k) ≡ k
∸-lemm3 .{(suc k)} {k} <-base rewrite ∸-lemm2 1 k = refl
∸-lemm3 .{(suc n)} {k} (<-step {n} y) with ∸-lemm3 y 
∸-lemm3 .{(suc n)} {k} (<-step {n} y) | p with ∸-lemm1 n k (<-step y)
... | prf1 rewrite prf1 | (∸-lemm1 (suc n) k (<-step (<-step y))) | ∸-lemm1 n k (<-step y) = p

∸-lemm4 : ∀ n k → (n ∸ k) < (suc n)
∸-lemm4 n zero = <-base
∸-lemm4 zero (suc n') = <-base
∸-lemm4 (suc n) (suc n') = <-step (∸-lemm4 n n')

∸-lemm5 : ∀ i j n → (suc i) + (suc j) ≡ n → n ∸ (suc i) ≡ (suc j)
∸-lemm5 zero j .(suc (suc j)) refl = refl
∸-lemm5 (suc n) j .(suc (suc (n + suc j))) refl 
 = ∸-lemm5 n j (suc n + suc j) refl

∸-lemm6 : ∀ {i n j} → suc j ≡ n ∸ i → j ≡ n ∸ (suc i)
∸-lemm6 {zero} {zero} {j} ()
∸-lemm6 {(suc n)} {zero} {j} ()
∸-lemm6 {zero} {(suc n)} {j} p = cong (λ x → x ∸ 1) p
∸-lemm6 {(suc n)} {(suc n')} {j} p = ∸-lemm6 {n} {_} {j} p

∸-lemm7 : ∀ i j n → suc i + suc j ≡ suc n → j ≡ n ∸ suc i
∸-lemm7 i j n p with sym (∸-lemm5 i j (suc n) p) 
... | prf =  ∸-lemm6 {i} prf

∸-lemm8 : ∀ i a → i + a ∸ i ≡ a
∸-lemm8 zero a = refl
∸-lemm8 (suc i₁) a = ∸-lemm8 i₁ a

∸-lemm9 : ∀ {n i q1 p1} →  (n + i) ≡ q1 + (p1 + i) → (p1 + q1) ≡ n
∸-lemm9 {n} {i} {q1} {p1} p 
 rewrite +-comm n i 
 | +-comm p1 i 
 | sym (+-assoc q1 i p1) 
 | +-comm q1 i  
 | +-assoc i q1 p1 with 
 cong (λ t → t ∸ i) p 
... | c 
 rewrite ∸-lemm8 i n 
 |  ∸-lemm8 i (q1 + p1) = +-comm-sum {q1} (sym c)

∸-lemm10 : ∀ {i n} → i ≡ (suc i + n) → ⊥
∸-lemm10 {zero} {n} ()
∸-lemm10 {suc i} {n} p = ∸-lemm10 {i} (cong pred p)

∸-lemm11 : ∀ {i q1 p1} → suc i ≡ suc (i + q1 + suc p1) → ⊥
∸-lemm11 {zero} {zero} {p1} ()
∸-lemm11 {zero} {suc q1} {p1} ()
∸-lemm11 {suc i} {q1} {p1} p = ∸-lemm11 {i} (cong pred p)
