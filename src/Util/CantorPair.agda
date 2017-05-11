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


{-


helper : (x a b : ℕ) → (a≢0 : a ≢ 0) → (b≢0 : b ≢ 0) → x ℕ.< a * b → (x div b) {fromWitnessFalse b≢0} ℕ.< a × (x div a) {fromWitnessFalse a≢0} ℕ.< b
helper x zero b a≢0 b≢0 x<a*b = ⊥-elim (a≢0 refl)
helper x (suc a) zero a≢0 b≢0 x<a*b = ⊥-elim (b≢0 refl)
helper x (suc a) (suc b) a≢0 b≢0 x<a*b = {!c!}
{-
helper zero m a x x₁ x₂ = ⊥-elim (x refl)
helper (suc n) zero a x x₁ x₂ = ⊥-elim (x₁ refl)
helper (suc n) (suc m) a x x₁ (s≤s x₂) = {!!} , {!!}
 where
  g : suc (div-helper 0 n a n) ℕ.≤ suc m
  g with div-helper 0 n a n
  g | zero = s≤s z≤n
  g | suc q = {!!}
-}
-- n ≠ 0, m ≠ 0, a < n * m geeft  a / m < n  en a / n < m
-- suc (div-helper 0 b x b) ℕ.≤ suc a


\-on-< : (x a b : ℕ) → (b≢0 : b ≢ 0) → x ℕ.< a * b → (x div b) {fromWitnessFalse b≢0} ℕ.< a
\-on-< x a zero b≢0 x₁ = ⊥-elim (b≢0 refl)
\-on-< x a (suc b) b≢0 x₁ = {!!}

-- div-helper 0 b x b ℕ.< a

-- we zijn op zoek naar een invariant
-- omdat we zelf een k kunnen invullen, en het niet persee zo is dat k altijd op 0 begint, moeten we een extra eis toevoegen.

--  namelijk       k             n div m + k * m ≡ ORGINEEL             (  + j  )
-- ook een eis dat j ≤ m.

--  n < a * m
-- div-helper 0 m n m < a.

-- maar dan moeten we ook wat zeggen over k op de plek van 0.
-- div-helper k m n j < a → j ≤ m → (k + div-helper 0 m n m) * m + j ≡ o
-- k < n,   n < a * (b - k?)
-- a / b * b + a % b ≡ a

-- x < a * b   →    x / b < a

mod-lemma₁ : (o acc d n : ℕ) →
              let s = acc ℕ.+ n in
              (acc ℕ.+ n ≡ o) →
              mod-helper acc s d n ℕ.+ n ≡ o
mod-lemma₁ o acc zero n x = x
mod-lemma₁ o acc (suc d) zero x = {!mod-lemma₁ o zero d (acc ℕ.+ 0) x!}  --mod-lemma₁ zero d (acc ℕ.+ 0) {!!}
mod-lemma₁ o acc (suc d) (suc n) x = {!!}              

mod-lemma₂ : (mod-acc d m : ℕ) → mod-helper mod-acc d m zero ≡ mod-acc
mod-lemma₂ mod-acc d zero = refl
mod-lemma₂ mod-acc d (suc m) = {!!}
{-
mod-helper : Nat → Nat → Nat → Nat → Nat
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j


div-helper k m (suc n) (suc j) = div-helper k m n j
-}






div-lemma :
    (mod-acc mod-acc₂ div-acc div-acc₂ n m b : ℕ) →
    let s₁ = mod-acc ℕ.+ b
        s₂ = mod-acc₂ ℕ.+ b in
    (n ℕ.≤ m) →
    (div-acc ℕ.≤ div-acc₂) → 
    
    div-helper div-acc s₁ n b ℕ.≤ div-helper div-acc₂ s₂ m b
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero zero b x x₁ = x₁
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero (suc m) zero x x₁ = let a = division-lemma mod-acc₂ (suc div-acc₂) m zero in {!mod-lemma mod-acc₂ m zero!}  -- div-lemma mod-acc mod-acc₂ div-acc (suc div-acc₂) zero m zero
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero (suc m) (suc b) x x₁ = {!!}
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ (suc n) m b x x₁ = {!!}

{-
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero zero b x q = q -- ≤′⇒≤ ≤′-refl
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero (suc m) zero x q = {!div-lemma mod-acc mod-acc₂ div-acc (suc div-acc₂) ? ? 0!}
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ zero (suc m) (suc b) x q = {!!} -- div-lemma 0 div-acc (suc (div-acc₁)) {!mod-acc ℕ.+ 0!} {!mod-acc ℕ.+ 0!} b a {!!}
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ (suc n) zero b () q
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ (suc n) (suc m) zero (s≤s x) q = {!div-lemma mod-acc mod-acc₂ (suc div-acc) n m (mod-acc ℕ.+ 0) x!}
div-lemma mod-acc mod-acc₂ div-acc div-acc₂ (suc n) (suc m) (suc b) x q = {!!}
-}
{-
div-helper-lemma₃ : ( dividend dividend-dec quotient-acc divisor remainder-dec : ℕ) → div-helper quotient-acc divisor dividend-dec remainder-dec
div-helper-lemma₃ = {!!}

(a o k b n j : ℕ) → (div-helper 0 b n b ℕ.+ k) ℕ.* b ℕ.+ b ℕ.∸ j ≡ o   div-helper k b n j ≡ {!!}
div-helper-lemma₃ = {!!}
-}

{-    divisor-1  dividend 
   initial   |   /  divisor -1
          \  |  /  /
div-helper 0 4 16 4


div-helper : Nat → Nat → Nat → Nat → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j
-}
exa : {x y u : ℕ} → {u≢0 : False (u ℕ.≟ 0)} → x ℕ.≤ y → (x div u) {u≢0} ℕ.≤ (y div u) {u≢0}
exa {x} {y} {zero} {u≢0} x≤y = ⊥-elim u≢0
exa {x} {y} {suc u} {u≢0} x≤y = let a = subst (λ r → mod-helper 0 u x u ℕ.+ div-helper 0 u x u * suc u ℕ.≤ r) (division-lemma 0 0 y u) (subst (λ r → r ℕ.≤ y) (division-lemma 0 0 x u) x≤y) in div-lemma 0 0 0 0 x y u x≤y {!!}


{-
mod-acc ℕ.+ div-acc₁ * suc (mod-acc ℕ.+ b) ℕ.≤
mod-helper mod-acc (mod-acc ℕ.+ b) (suc m) b ℕ.+
div-helper div-acc₁ (mod-acc ℕ.+ b) (suc m) b * suc (mod-acc ℕ.+ b)



division-lemma zero (suc div-acc) d s

  mod-lemma : (acc d n : ℕ) →
              let s = acc + n in
              mod-helper acc s d n ≤ s

  mod-lemma acc zero n = start
    acc      ≤⟨ m≤m+n acc n ⟩
    acc + n  □

  mod-lemma acc (suc d) zero = start
    mod-helper zero (acc + 0) d (acc + 0)  ≤⟨ mod-lemma zero d (acc + 0) ⟩
    acc + 0                                □

  mod-lemma acc (suc d) (suc n) =
    P.subst (λ x → mod-helper (suc acc) x d n ≤ x)
            (P.sym (+-suc acc n))
            (mod-lemma (suc acc) d n)


exa {x} {y} {zero} {v} {u≢0} {v≢0} x₁ x₂ = ⊥-elim u≢0
exa {x} {y} {suc u} {zero} {u≢0} {v≢0} x₁ x₂ = ⊥-elim v≢0
exa {x} {y} {suc u} {suc v} {u≢0} {v≢0} x₁ (s≤s x₂) = let p = subst (λ r → mod-helper 0 u x u ℕ.+ div-helper 0 u x u * suc u ℕ.≤ r) (division-lemma 0 0 y v) (subst (λ r → r ℕ.≤ y) (division-lemma 0 0 x u) x₁) in {!mod-lemma 0 x u !} -}
-- y ≡ mod-helper 0 v y v ℕ.+ div-helper 0 v y v * suc v

-- mod-helper 0 u x u ℕ.≤ u
-- mod-helper 0 v y v ℕ.≤ v
-- mod-helper 0 u x u ℕ.+ div-helper 0 u x u * suc u ℕ.≤ mod-helper 0 v y v ℕ.+ div-helper 0 v y v * suc v
-- 

_div-mono_ : ℕ._*_ Preserves₂ ℕ._≤_ ⟶ ℕ._≤_ ⟶ ℕ._≤_
_div-mono_ = {!!}

div-helper-lemma₂ : (a o k b n j : ℕ) → o ℕ.< a * b → j ℕ.≤ b → (div-helper 0 b n b ℕ.+ k) ℕ.* b ℕ.+ b ℕ.∸ j ≡ o → div-helper k b n j ℕ.< a
div-helper-lemma₂ a o k b zero j x x₁ q = {!!}
div-helper-lemma₂ a o k b (suc n) zero x x₁ q = div-helper-lemma₂ a o (suc k) b n b {!!} {!!} {!!} 
div-helper-lemma₂ a o k b (suc n) (suc j) x x₁ q = div-helper-lemma₂ a o k b n j {!!} {!!} {!!}

div-helper₁ : (n a b : ℕ) → n ℕ.< a ℕ.* b → div-helper 0 b n b ℕ.< a
div-helper₁ n a b x with division-lemma 0 0 n b
... | q = {!!}




-- = div-helper-lemma₂ a n 0 b n b x {!!} {!!} 


toℕ-fromℕ≤″ : ∀ {m n} (m<n : m ℕ.<″ n) → 𝔽.toℕ (fromℕ≤″ m m<n) ≡ m
toℕ-fromℕ≤″ {m} {n} m<n =
 begin
  𝔽.toℕ (fromℕ≤″ m m<n)
 ≡⟨ cong 𝔽.toℕ (sym (fromℕ≤≡fromℕ≤″ (≤″⇒≤ m<n) m<n)) ⟩
  𝔽.toℕ (fromℕ≤ (≤″⇒≤ m<n))
 ≡⟨ toℕ-fromℕ≤ (≤″⇒≤ m<n) ⟩
  m
 ∎

div-helper₀ : (a b : ℕ) → {b≢0 : False (b ℕ.≟ 0)} → 𝔽.toℕ ((a mod b) {b≢0}) ℕ.+  (a div b) {b≢0} ℕ.* b ≡ a 
div-helper₀ a zero {b≢0} = ⊥-elim b≢0
div-helper₀ a (suc b) {b≢0} = trans (cong (λ section → section ℕ.+ div-helper 0 b a b * suc b)
                                     {𝔽.toℕ
                                      (fromℕ≤″ (mod-helper 0 b a b)
                                       (erase (≤⇒≤″ (s≤s (mod-lemma 0 a b)))))}
                                     {mod-helper 0 b a b} (toℕ-fromℕ≤″ (erase (≤⇒≤″ (s≤s (mod-lemma 0 a b)))))) (sym (division-lemma 0 0 a b)) 
{-
mod-helper 0 b a b ℕ.+ div-helper 0 b a b * suc b ≡ a


mod-helper 0 b a b ℕ.+ div-helper 0 b a b * suc b ≡ a
-}
open import Data.Nat.Properties.Simple
div-z :
    (mod-acc div-acc d n c : ℕ) →
    let s = mod-acc ℕ.+ n in
    c ℕ.* (mod-acc ℕ.+ div-acc ℕ.* suc s ℕ.+ d)
      ≡
    mod-helper mod-acc s d n ℕ.+ div-helper div-acc s (c ℕ.* (mod-acc ℕ.+ div-acc ℕ.* suc s ℕ.+ d)) n
div-z mod-acc div-acc d n c = {!!}




div-helper₄ : (m n : ℕ) → div-helper m 0 n 0 ≡ m ℕ.+ (div-helper 0 0 n 0)
div-helper₄ zero n = refl
div-helper₄ (suc m) zero = sym (cong suc (+-right-identity m))
div-helper₄ (suc m) (suc n) = trans (div-helper₄ (suc (suc m)) n) (cong suc (trans (sym (+-suc m (div-helper 0 0 n 0))) (cong (ℕ._+_ m) (sym (div-helper₄ 1 n)))))

eee : (a b : ℕ) → div-helper 0 b (a * suc b) b ≡ a
eee zero b = refl
eee (suc a) zero rewrite *-comm a 1 | +-right-identity a = trans (div-helper₄ 1 a) (cong suc (subst (λ y → div-helper 0 0 y 0 ≡ a) (trans (*-comm a 1) (+-right-identity a)) (eee a zero)) )
eee (suc a) (suc b) = {!eee a (suc b)!} --  let q = eee a b in trans {!!} (cong suc q) -- rewrite *-comm a (suc b) = trans {!!} (cong suc (eee a b))
 
-- rewrite *-comm a (suc b) = {!a!}



div-helper₇ : (a b : ℕ) → {b≢0 : False (b ℕ.≟ 0)} → ((a * b) div b) {b≢0} ≡ a 
div-helper₇ a zero {b≢0} = ⊥-elim b≢0
div-helper₇ a (suc b) {b≢0} = {!!}

div-helper₆ : (a b : ℕ) → {b≢0 : False (b ℕ.≟ 0)} → 𝔽.toℕ ((a mod b) {b≢0}) ℕ.+  ((a * b) div b) {b≢0} ≡ a 
div-helper₆ a zero {b≢0} = ⊥-elim b≢0
div-helper₆ a (suc b) {b≢0} = trans (cong (λ section → section ℕ.+ div-helper 0 b (a * suc b) b)
                                     {𝔽.toℕ
                                      (fromℕ≤″ (mod-helper 0 b a b)
                                       (erase (≤⇒≤″ (s≤s (mod-lemma 0 a b)))))}
                                     {mod-helper 0 b a b} (toℕ-fromℕ≤″ (erase (≤⇒≤″ (s≤s (mod-lemma 0 a b)))))) {!sym (div-z 0 0 a b b) -- sym (division-lemma 0 0 a b)!}





div-≤ : (div-acc m n j : ℕ) → div-acc ℕ.≤ div-helper div-acc m n j
div-≤ div-acc m zero j = ≤′⇒≤ ≤′-refl
div-≤ div-acc m (suc n) zero = ≤-trans (≤-step (≤′⇒≤ ≤′-refl)) (div-≤ (suc div-acc) m n m)
div-≤ div-acc m (suc n) (suc j) = div-≤ div-acc m n j


div-≤₁ : (div-acc₁ div-acc₂ m₁ m₂ n j : ℕ) → m₁ ℕ.≤ m₂  → div-acc₁ ℕ.≤ div-acc₂ → div-helper div-acc₁ n m₁ j ℕ.≤ div-helper div-acc₂ n m₂ j
div-≤₁ div-acc₁ div-acc₂ zero m₂ n j x x₁ = ≤-trans x₁ (div-≤ div-acc₂ n m₂ j) 
div-≤₁ div-acc₁ div-acc₂ (suc m₁) zero n j () x₁
div-≤₁ div-acc₁ div-acc₂ (suc m₁) (suc m₂) n zero (s≤s x) x₁ = div-≤₁ (suc div-acc₁) (suc div-acc₂) m₁ m₂ n n x (s≤s x₁)
div-≤₁ div-acc₁ div-acc₂ (suc m₁) (suc m₂) n (suc j) (s≤s x) x₁ = div-≤₁ div-acc₁ div-acc₂ m₁ m₂ n j x x₁

div-mono : {x y : ℕ} → (u : ℕ) → {u≢0 : False (u ℕ.≟ 0)} → x ℕ.≤ y → (x div u) {u≢0} ℕ.≤ (y div u) {u≢0}
div-mono {x} {y} zero {u≢0} x≤y = ⊥-elim u≢0
div-mono {x} {y} (suc u) {u≢0} x≤y = div-≤₁ 0 0 x y u u x≤y z≤n


div-helper₃ : (n : ℕ) → div-helper 0 0 n 0 ≡ n
div-helper₃ zero = refl
div-helper₃ (suc n) = trans (div-helper₄ 1 n) (cong suc (div-helper₃ n))

div-helper-*-div : (m n k : ℕ) → div-helper 0 m n m * k ≡ n * div-helper 0 m k m
div-helper-*-div zero n k rewrite div-helper₃ n | div-helper₃ k = refl
div-helper-*-div (suc m) zero k = refl
div-helper-*-div (suc m) (suc n) k = {!div-helper-*-div (suc (suc m)) n k!}
open SemiringSolver
--  ≡⟨ solve 3 (λ n a b → n :- a :+ (b :- n) , b :- a) (λ {x} {x₁} {x₂} → refl) (+ n) (+ a) (+ b)
div-helper-*-div₂ : (m n k : ℕ) → n * div-helper 0 m k m ≡ div-helper 0 m n m * k
div-helper-*-div₂ m zero k = refl
div-helper-*-div₂ zero (suc n) zero = trans (*-comm n 0) (sym (*-comm (div-helper 1 0 n 0) 0))
div-helper-*-div₂ zero (suc n) (suc k) rewrite div-helper₄ 1 k | div-helper₄ 1 n = let a = div-helper-*-div₂ 0 n k in
 cong suc (trans (cong (ℕ._+_ (div-helper 0 0 k 0)) (+-*-suc n (div-helper 0 0 k 0))) {!!})
-- cong suc (SemiringSolver.solve 4 (λ n k dn dk → dk :+ n :* (con 1 :+ dk) , k :+ dn :* (con 1 :+ k)) {!!} n k (div-helper 0 0 n 0) (div-helper 0 0 k 0))
-- div-helper 0 0 k 0 ℕ.+ n * suc (div-helper 0 0 k 0) ≡  k ℕ.+ div-helper 0 0 n 0 * suc k
div-helper-*-div₂ (suc m) (suc n) zero = trans (*-comm n 0) (sym (*-comm (div-helper 0 (suc m) n m) 0))
div-helper-*-div₂ (suc m) (suc n) (suc k) = {!div-helper-*-div₂ m n k!}



*-div : (n m k : ℕ) → {m≢0 : False (m ℕ.≟ 0)} →  (n div m) {m≢0} * k ≡ n * (k div m) {m≢0}
*-div n zero k {m≢0} = ⊥-elim m≢0
*-div n (suc m) k = div-helper-*-div m n k


div-lemma₅ : (m : ℕ) → (j : ℕ) → j ℕ.≤ m → div-helper 0 m (suc m) j ≡ 1
div-lemma₅ zero .0 z≤n = refl
div-lemma₅ (suc m) zero p = {!div-lemma₅ m m !}
div-lemma₅ (suc m) (suc j) p = {!div-lemma₅ (suc m) j ?!}


-- div-≤ : (div-acc m n j : ℕ) →  ℕ.≤ div-helper div-acc m n j

div-l :
    (mod-acc div-acc d n : ℕ) →
    let s = mod-acc ℕ.+ n in
    mod-acc ℕ.+ d ≡ n
    → div-acc ≡ {!!}
    →
    mod-acc ℕ.+ div-acc ℕ.* suc s ℕ.+ d
      ≡
    mod-helper mod-acc s d n ℕ.+ div-helper div-acc s d n ℕ.* suc s
    → div-helper div-acc s d n ≡ 1
div-l mod-acc div-acc zero n x x₁ r = {!!}
div-l mod-acc div-acc (suc d) n x x₁ r = {!!}


-- 1 ℕ.≤ div-helper 0 m (suc m) m

--  mod-acc + div-acc * suc s + d  ≡  mod-helper mod-acc s d n + div-helper div-acc s d n * suc s
div-t : (mod-acc div-acc d n : ℕ) →
         let s = n ℕ.+ mod-acc in
         suc s ℕ.≤ d ℕ.+ mod-acc ℕ.+ suc s ℕ.* div-acc 
         → 1 ℕ.≤ div-helper div-acc s d n
div-t zero div-acc zero zero x rewrite (+-right-identity div-acc) = x
div-t (suc mod-acc) div-acc zero zero (s≤s x) = div-t mod-acc div-acc zero zero {!x!}
div-t mod-acc div-acc zero (suc n) x = {!!}
div-t mod-acc div-acc (suc d) n x = {!!}



m-div-m : (m : ℕ) → {m≢0 : False (m ℕ.≟ 0)} → (m div m) {m≢0} ℕ.≤ 1
m-div-m zero {m≢0} = ⊥-elim m≢0
m-div-m (suc m) {m≢0} = {!div-t 0 0 (suc m) m !}


open ≤-Reasoning 
lemma₅ : {n m k : ℕ} → {m≢0 : False (m ℕ.≟ 0)} → k ℕ.≤ n * m → (k div m) {m≢0} ℕ.≤ n
lemma₅ {n} {m} {k} {m≢0} k≤n*m = ≤-trans (div-mono m {m≢0} k≤n*m) {!_*-mono_ (≤′⇒≤ (≤′-refl {n})) (m-div-m m {m≢0}) !}

lemma₃ : {n m k : ℕ} → {m≢0 : False (m ℕ.≟ 0)} → k ℕ.< n * m → (k div m) {m≢0} ℕ.< n
lemma₃ {n} {m} {k} {m≢0} k<n*m = {!!}
{-
≤-Reasoning.begin
  suc (k div m)
  ≤⟨ {!!} ⟩
  (suc k) div m
  ≤⟨ div-mono m {m≢0} k<n*m ⟩
  n * m div m
  ≤⟨ n≤m+n (𝔽.toℕ ((n mod m) {m≢0})) (n * m div m) ⟩
  𝔽.toℕ (n mod m) ℕ.+ n * m div m
  ≤-Reasoning.≡⟨ div-helper₆ n m {m≢0} ⟩
  {-
  n 
  ≤-Reasoning.≡⟨ {!!} ⟩ 
  𝔽.toℕ ((n mod m) {m≢0}) ℕ.+ n * (m div m) {m≢0}
  ≤-Reasoning.≡⟨ cong (ℕ._+_ (𝔽.toℕ ((n mod m) {m≢0}))) (sym (*-div n m m {m≢0})) ⟩
  𝔽.toℕ ((n mod m) {m≢0}) ℕ.+ (n div m) {m≢0} * m
  ≤-Reasoning.≡⟨ div-helper₀ n m {m≢0} ⟩ -}
  n
  ≤-Reasoning.∎ -}
-- begin div-helper₀ n m {m≢0} -- 
lemma : (n m k : ℕ) → (n≢0 : n ≢ 0) → k ℕ.< n * m → (k div n) {fromWitnessFalse n≢0} ℕ.< m
lemma zero m k x x₁ = ⊥-elim (x refl)
lemma (suc n) m k x x₁ = div-helper₁ k m n {!!}

open import Data.Unit
open CommutativeSemiring commutativeSemiring using (*-comm)
𝔽-to-𝔽×𝔽 : {n m : ℕ} → Fin (n * m) → (Fin n × Fin m)
𝔽-to-𝔽×𝔽 {zero} {m} ()
𝔽-to-𝔽×𝔽 {suc n} {m} x with ((𝔽.toℕ x) divMod (suc n)) {tt}
𝔽-to-𝔽×𝔽 {suc n} {m} x | result quotient remainder property = remainder , fromℕ≤ {quotient} q<m
 where
  postulate
   q<m : quotient ℕ.< m



open import Relation.Binary.PropositionalEquality.TrustMe
𝔽↔𝔽×𝔽 : (n m : ℕ) → (Fin n × Fin m) ↔ (Fin (n * m))
to (𝔽↔𝔽×𝔽 n m) = →-to-⟶ 𝔽×𝔽-to-𝔽
from (𝔽↔𝔽×𝔽 n m) = →-to-⟶ 𝔽-to-𝔽×𝔽
left-inverse-of (inverse-of (𝔽↔𝔽×𝔽 n m)) x = trustMe
right-inverse-of (inverse-of (𝔽↔𝔽×𝔽 n m)) x = trustMe


-- (fromℕ≤ (proj₁ (helper (𝔽.toℕ x) n m {!!} {!!} (bounded x)))) , {!!}
{- ith ((𝔽.toℕ x) divMod n) {{!!}}
𝔽-to-𝔽×𝔽 {n} {m} x | result quotient remainder property = remainder , {!quotient!}
-}


{-
div-helper-lemma₁ k m zero j n x = {!!}
div-helper-lemma₁ k m (suc r) zero n x = div-helper-lemma₁ (suc k) m r m n x
div-helper-lemma₁ k m (suc r) (suc j) n x = div-helper-lemma₁ k m r j n x -}
{- n m zero r n≢0 x = z≤n
div-helper-lemma₁ n m (suc k) zero n≢0 x = {!div-helper!}
div-helper-lemma₁ n m (suc k) (suc r) n≢0 x = {!!}
-}
-- g : div-helper 1 
{-





next : (n : ℕ) → (Fin n × Fin m) ↔ Fin (n * m)
next n = record
 { to = →-to-⟶ (λ{ (a , b) → fromℕ≤ {ℕ×ℕ-to-ℕ (𝔽.toℕ a , 𝔽.toℕ b)} {n * n} {!!}})
 ; from = →-to-⟶ (λ x → (fromℕ≤ {proj₁ (ℕ-to-ℕ×ℕ (𝔽.toℕ x))} {n} {!!}) , (fromℕ≤ {proj₂ (ℕ-to-ℕ×ℕ (𝔽.toℕ x))} {n} {!!}))
 ; inverse-of = record
  { left-inverse-of = λ x → {!!}
  ; right-inverse-of = {!!}
  }
 }
-}

-}
