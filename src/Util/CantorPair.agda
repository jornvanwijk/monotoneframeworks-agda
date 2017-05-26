---
-- Cantor pairing function
-- inspired by http://www.lix.polytechnique.fr/coq/pylons/contribs/files/Goedel/v8.4/Goedel.cPair.html
---
module Util.CantorPair where

open import Data.Product hiding (map)
open import Data.List hiding (all)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat as ℕ
open import Data.List.Any hiding (index)
open import Relation.Binary
open import Function.Inverse hiding (sym)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans ; refl to ≤-refl)
open import Util.Sum
open import Data.Empty
open import Function.Injection
open import Function.Surjection
open import Function.Bijection 
open import Function 
open import Util.Product
open import Data.Sum
open import Data.Nat.Properties
open import Util.Nat
open import Relation.Nullary.Negation
open import Data.Stream

sumToN : (n : ℕ) → ℕ
sumToN zero = zero
sumToN (suc n) = suc n + sumToN n

sumToN1 : {n : ℕ} → n ≤ sumToN n
sumToN1 {zero} = z≤n
sumToN1 {suc n} = m≤m+n (suc n) (sumToN n)

sumToN2 : {a b : ℕ} → a ≤ b → sumToN a ≤ sumToN b
sumToN2 {.0} {b} z≤n = z≤n
sumToN2 {.(suc _)} {.(suc _)} (s≤s p) = s≤s (p +-mono (sumToN2 p))

sumToN3 : (a : ℕ) → sumToN a ≡ 0 → a ≡ 0
sumToN3 zero refl = refl
sumToN3 (suc a) ()

sumToN3′ : sumToN 0 ≡ 0
sumToN3′ = refl

sumToN4 : (a : ℕ) → sumToN a ≡ 1 → a ≡ 1
sumToN4 zero ()
sumToN4 (suc zero) refl = refl
sumToN4 (suc (suc a)) ()


open StrictTotalOrder strictTotalOrder using (_<?_)
open DecTotalOrder decTotalOrder using () renaming (antisym to ≤-antisym)

module ℤ where
  open import Data.Integer public
  open import Util.Integer public
open ℤ using (ℤ)

{-
probleem

we willen laten zien dat sumToN  een inverse heeft  (i.e.   sumToN-inverse (sumToN n) = n  )

Nu doen we dit door middel van een lokale functie die vanaf m begint, en vervolgens steeds kleiner wordt totdat de som kleiner is dan m.

sumToN-inverse : (m : ℕ) → ℕ
sumToN-inverse m = g m
 where
  g : (x : ℕ) → ℕ
  g zero = 0 
  g (suc x) with sumToN (suc x) ≤? m
  g (suc x) | yes p = (suc x) 
  g (suc x) | no ¬p = g x

omdat g lokaal is aan sumToN, kunnen we op andere plekken niets over g bewijzen want die is niet in scope.
dit kunnen we op minstens twee manieren oplossen:
  vervang where door: module L where
  dan komt g in global scope als:  L.g : (m : ℕ) → (x : ℕ) → ℕ
  bij een aanroep sumToN-inverse 5 zijn we dan wel informatie verloren, namelijk dat er altijd een L.g 5 bij hoort.
  en impliciet ook dat voor alle x geldt dat x ≤ m  (of in dit geval x ≤ 5). 

  de andere oplossing is om g globaal te definieren maar private, je houdt dan bovenstaand probleem.

  Ik vermoed dat dit probleem in een AG oplossing niet speelt, dan zouden we immers ergens losstaand een 'knoop' kunnen maken die laat zien dat x ≤ m.
  We kunnen er ook voor kiezen om dus maar een grote functie te maken met alle bewijzen ge-embed.
  De code wordt er daardoor complexer op omdat allerlei bewijzen door elkaar heen gegeven worden. (zie het mfp bewijs en verschillende invarianten)
  Daarnaast krijg je een probleem bij bewijzen over combinaties van functies.
-}

find-sum-≤-m : (m : ℕ) → (x : ℕ) → ℕ
find-sum-≤-m m x with sumToN x ≤? m
find-sum-≤-m m x | yes p = x
find-sum-≤-m m zero | no ¬p = 0
find-sum-≤-m m (suc x) | no ¬p = find-sum-≤-m m x

sumToN-inverse : (m : ℕ) → ℕ
sumToN-inverse m = find-sum-≤-m m m

find-sum-≤-m-lemma₁ : (m : ℕ) → (x : ℕ) → sumToN (find-sum-≤-m m x) ≤ m
find-sum-≤-m-lemma₁ m x with sumToN x ≤? m
find-sum-≤-m-lemma₁ m x | yes p = p
find-sum-≤-m-lemma₁ m zero | no ¬p = contradiction z≤n ¬p
find-sum-≤-m-lemma₁ m (suc x) | no ¬p = find-sum-≤-m-lemma₁ m x

sumToN-inverse-lemma₁ : (m : ℕ) → sumToN (sumToN-inverse m) ≤ m
sumToN-inverse-lemma₁ m = find-sum-≤-m-lemma₁ m m

find-sum-≤-m-lemma₂ : (m : ℕ) → (x : ℕ) → ((k : ℕ) → k > x → sumToN k ≥ m) → (k : ℕ) → k > find-sum-≤-m m x → sumToN k ≥ m
find-sum-≤-m-lemma₂ m x r k x₁ with sumToN x ≤? m
find-sum-≤-m-lemma₂ m x r k x₁ | yes p = r k x₁
find-sum-≤-m-lemma₂ m zero r k x₁ | no ¬p = contradiction z≤n ¬p
find-sum-≤-m-lemma₂ m (suc x) r k x₁ | no ¬p = find-sum-≤-m-lemma₂ m x (λ k x₁ → case suc x ≟ k of (λ{ (yes refl) → ≤-trans (≤-step ≤-refl) (≰⇒> ¬p) ; (no ¬p₁) → r k (≤∧≠⇒< x₁ ¬p₁)})) k x₁

sumToN-inverse-lemma₂ : (m : ℕ) → (k : ℕ) → k > sumToN-inverse m → sumToN k ≥ m
sumToN-inverse-lemma₂ m k x = find-sum-≤-m-lemma₂ m m (λ k₁ x₁ → ≤-trans (≤-trans (≤-step ≤-refl) x₁) (sumToN1 {k₁})) k x

open import Data.Integer.Properties
open ≡-Reasoning
find-sum-≤-m-lemma₃ : (m : ℕ) → (x : ℕ) → Σ[ r ∈ ℕ ] r + sumToN (find-sum-≤-m m x) ≡ m
find-sum-≤-m-lemma₃ m x  with sumToN x ≤? m
find-sum-≤-m-lemma₃ m x | yes p = m ∸ sumToN x , a∸b+b≡a m (sumToN x) p 
find-sum-≤-m-lemma₃ m zero | no ¬p = contradiction z≤n ¬p
find-sum-≤-m-lemma₃ m (suc x) | no ¬p = find-sum-≤-m-lemma₃ m x

sumToN-inverse-lemma₃ : (m : ℕ) → Σ[ r ∈ ℕ ] r + sumToN (sumToN-inverse m) ≡ m
sumToN-inverse-lemma₃ m = find-sum-≤-m-lemma₃ m m

find-sum-≤-m-lemma₄ : (m : ℕ) → (x : ℕ) → x ≤ m → sumToN (find-sum-≤-m m x) ≤ m
find-sum-≤-m-lemma₄ zero .0 z≤n = z≤n
find-sum-≤-m-lemma₄ (suc m) x x≤m with sumToN x ≤? suc m
find-sum-≤-m-lemma₄ (suc m) x x≤m | yes p = p
find-sum-≤-m-lemma₄ (suc m) zero x≤m | no ¬p = x≤m
find-sum-≤-m-lemma₄ (suc m) (suc x) x≤m | no ¬p = find-sum-≤-m-lemma₄ (suc m) x (≤-trans (≤-step ≤-refl) x≤m)

sumToN-inverse-lemma₄ : (m : ℕ) → sumToN (sumToN-inverse m) ≤ m
sumToN-inverse-lemma₄ m = find-sum-≤-m-lemma₄ m m ≤-refl

find-sum-≤-m-lemma₅ : (m : ℕ) → (x : ℕ) → x ≤ m → m ≤ x + sumToN x → m ≤ find-sum-≤-m m x + sumToN (find-sum-≤-m m x)
find-sum-≤-m-lemma₅ zero .0 z≤n z = z≤n
find-sum-≤-m-lemma₅ (suc m) x x≤m z with sumToN x ≤? suc m
find-sum-≤-m-lemma₅ (suc m) x x≤m z | yes p = z
find-sum-≤-m-lemma₅ (suc m) zero x≤m z | no ¬p = contradiction z≤n ¬p
find-sum-≤-m-lemma₅ (suc m) (suc x) x≤m z | no ¬p = find-sum-≤-m-lemma₅ (suc m) x (≤-trans (≤-step ≤-refl) x≤m) (≤-pred (≰⇒> ¬p)) 

sumToN-inverse-lemma₅ : (m : ℕ) → m ≤ sumToN-inverse m + sumToN (sumToN-inverse m)
sumToN-inverse-lemma₅ m = find-sum-≤-m-lemma₅ m m ≤-refl (m≤m+n m (sumToN m))

ℕ-to-ℕ×ℕ : ℕ → ℕ × ℕ
ℕ-to-ℕ×ℕ zero = 0 , 0
ℕ-to-ℕ×ℕ (suc n) = suc n ∸ sumToN (sumToN-inverse (suc n)) , (sumToN-inverse (suc n) + sumToN (sumToN-inverse (suc n))) ∸ (suc n)

ℕ-to-ℕ×ℕ-lemma₁ : (n : ℕ) → ℤ.+ proj₁ (ℕ-to-ℕ×ℕ n) ≡ n ℤ.⊖ sumToN (sumToN-inverse n)
ℕ-to-ℕ×ℕ-lemma₁ zero = refl
ℕ-to-ℕ×ℕ-lemma₁ (suc n) = sym (⊖-≥ (sumToN-inverse-lemma₄ (suc n)))

ℕ-to-ℕ×ℕ-lemma₂ : (n : ℕ) → ℤ.+ proj₂ (ℕ-to-ℕ×ℕ n) ≡ (sumToN-inverse n + sumToN (sumToN-inverse n)) ℤ.⊖ n
ℕ-to-ℕ×ℕ-lemma₂ zero = refl
ℕ-to-ℕ×ℕ-lemma₂ (suc n) = sym (⊖-≥ (sumToN-inverse-lemma₅ (suc n)))

ℕ×ℕ-to-ℕ : ℕ × ℕ → ℕ
ℕ×ℕ-to-ℕ (x , y) = x + sumToN (x + y)

lemma₁ : (a b : ℕ) → a < b → a + sumToN a < sumToN b
lemma₁ .0 .(suc _) (s≤s z≤n) = s≤s z≤n
lemma₁ .(suc _) .(suc (suc _)) (s≤s (s≤s x)) = s≤s (s≤s (x +-mono lemma₁ _ _ (s≤s x)))

lemma₂ : (a b c d : ℕ) → a ≤ c → b ≤ d → a + sumToN c ≡ b + sumToN d → c ≡ d
lemma₂ a b c d x x₁ x₂ with c ≤? d
lemma₂ a b c d x x₁ x₂ | yes c≤d with c ≟ d
lemma₂ a b c d x x₁ x₂ | yes c≤d | (yes c≡d) = c≡d
lemma₂ a b c d x x₁ x₂ | yes c≤d | (no c≠d) = contradiction x₂ (<⇒≠ (≤-steps b (≤-trans (s≤s (x +-mono ≤-refl)) (lemma₁ c d (≤∧≠⇒< c≤d c≠d)))))
lemma₂ a b c d x x₁ x₂ | no c≰d = contradiction x₂ (>⇒≠ (≤-steps a (≤-trans (s≤s (x₁ +-mono ≤-refl)) (lemma₁ d c (≰⇒> c≰d)))))

open Inverse
open _InverseOf_
open import Util.Integer
open import Algebra

ℕ×ℕ-to-ℕ-surjective : (ℕ × ℕ) ↠ ℕ
Surjection.to ℕ×ℕ-to-ℕ-surjective =  →-to-⟶ ℕ×ℕ-to-ℕ
Surjective.from (Surjection.surjective ℕ×ℕ-to-ℕ-surjective) = →-to-⟶ ℕ-to-ℕ×ℕ
Surjective.right-inverse-of (Surjection.surjective ℕ×ℕ-to-ℕ-surjective) n = ℤ≡-to-ℕ≡ (
 begin
 ℤ.+ (proj₁ (ℕ-to-ℕ×ℕ n) + sumToN (proj₁ (ℕ-to-ℕ×ℕ n) + proj₂ (ℕ-to-ℕ×ℕ n)))
 ≡⟨⟩
 ℤ.+ proj₁ (ℕ-to-ℕ×ℕ n) ℤ.+ ℤ.+ sumToN (proj₁ (ℕ-to-ℕ×ℕ n) + proj₂ (ℕ-to-ℕ×ℕ n))
 ≡⟨ cong (ℤ._+ ℤ.+ sumToN (proj₁ (ℕ-to-ℕ×ℕ n) + proj₂ (ℕ-to-ℕ×ℕ n))) (ℕ-to-ℕ×ℕ-lemma₁ n)  ⟩
 n ℤ.⊖ sumToN (sumToN-inverse n) ℤ.+ ℤ.+ sumToN (proj₁ (ℕ-to-ℕ×ℕ n) + proj₂ (ℕ-to-ℕ×ℕ n))
 ≡⟨ cong (λ y → n ℤ.⊖ sumToN (sumToN-inverse n) ℤ.+ ℤ.+ sumToN y) (ℤ≡-to-ℕ≡ (
   begin
   ℤ.+ (proj₁ (ℕ-to-ℕ×ℕ n) + proj₂ (ℕ-to-ℕ×ℕ n))
   ≡⟨⟩
   ℤ.+ proj₁ (ℕ-to-ℕ×ℕ n) ℤ.+ ℤ.+ proj₂ (ℕ-to-ℕ×ℕ n)
   ≡⟨ cong₂ ℤ._+_ (ℕ-to-ℕ×ℕ-lemma₁ n) (ℕ-to-ℕ×ℕ-lemma₂ n) ⟩
   (n ℤ.⊖ sumToN (sumToN-inverse n)) ℤ.+ ((sumToN-inverse n + sumToN (sumToN-inverse n)) ℤ.⊖ n) 
   ≡⟨ ℤ⊖-outside n (sumToN (sumToN-inverse n)) (sumToN-inverse n + sumToN (sumToN-inverse n)) ⟩
   sumToN-inverse n + sumToN (sumToN-inverse n) ℤ.⊖ sumToN (sumToN-inverse n)
   ≡⟨ ℤ⊖-' (sumToN-inverse n) (sumToN (sumToN-inverse n)) ⟩
   ℤ.+ sumToN-inverse n
   ∎)) ⟩
 n ℤ.⊖ sumToN (sumToN-inverse n) ℤ.+ ℤ.pos (sumToN (sumToN-inverse n))
 ≡⟨ ℤ⊖- n (sumToN (sumToN-inverse n)) ⟩
 ℤ.pos n
 ∎)

ℕ×ℕ-to-ℕ-injective : (ℕ × ℕ) ↣ ℕ
Injection.to ℕ×ℕ-to-ℕ-injective = →-to-⟶ ℕ×ℕ-to-ℕ
Injection.injective ℕ×ℕ-to-ℕ-injective {a , b} {c , d} x =
  ≡×⇒≡ ( proj₁-≡ , proj₂-≡)
 where
  proj₁-≡ : a ≡ c
  proj₁-≡ = cancel-+-right (sumToN (c + d)) (subst (λ r → a + sumToN r ≡ c + sumToN (c + d)) (lemma₂ a c (a + b) (c + d) (m≤m+n a b) (m≤m+n c d) x) x)
  proj₂-≡ : b ≡ d
  proj₂-≡ = cancel-+-left c (subst (λ r → r + b ≡ c + d) proj₁-≡ (lemma₂ a c (a + b) (c + d) (m≤m+n a b) (m≤m+n c d) x))
  
ℕ×ℕ↔ℕ : (ℕ × ℕ) ↔ ℕ
ℕ×ℕ↔ℕ = fromBijection (record
 { to = →-to-⟶ ℕ×ℕ-to-ℕ
 ; bijective = record
  { injective = Injection.injective ℕ×ℕ-to-ℕ-injective
  ; surjective = Surjection.surjective ℕ×ℕ-to-ℕ-surjective }
 })



open import Data.Fin as 𝔽
open import Data.Nat.Properties
open import Data.Fin.Properties
𝔽×𝔽-to-𝔽 : {n m : ℕ} → (Fin n × Fin m) → Fin (n * m)
𝔽×𝔽-to-𝔽{n} {m} (a , b) = fromℕ≤ {𝔽.toℕ a * 𝔽.toℕ b} {n * m} (≤-trans (s≤s (m≤n⇒m≤k+n {𝔽.toℕ a * 𝔽.toℕ b} {𝔽.toℕ a * suc (𝔽.toℕ b)} (≤-refl {𝔽.toℕ a} *-mono ≤-step ≤-refl) (𝔽.toℕ b))) (bounded a *-mono bounded b))

open import Data.Nat.DivMod
open import Relation.Nullary.Decidable
open import Agda.Builtin.Nat

