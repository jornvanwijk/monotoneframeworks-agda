module Util.Fin-product2 where

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
open import Util.Integer
open import Algebra
open import Data.Integer.Properties
open ≡-Reasoning


module ℤ where
  open import Data.Integer public
  open import Util.Integer public
open ℤ using (ℤ)

open StrictTotalOrder strictTotalOrder using (_<?_)
open DecTotalOrder decTotalOrder using () renaming (antisym to ≤-antisym)

open import Data.Fin as 𝔽
open import Data.Nat.Properties
open import Data.Fin.Properties
open import Data.Nat.DivMod
open import Relation.Nullary.Decidable
open import Agda.Builtin.Nat

open Inverse
open _InverseOf_
open import Util.Integer
open import Algebra

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


{-
 a < b * n   →   a / b < n

 b * n / n  ≡  b ..


div-helper : Nat → Nat → Nat → Nat → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j

          mod-acc (divisor-1) dividend count
mod-helper : Nat → Nat → Nat → Nat → Nat
mod-helper k m  zero    j      = k                              <- if we get here; k ≡ 0;  because j must ≡ m. and we got here 
mod-helper k m (suc n)  zero   = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

k ≡ 0   of n > (m - j)
-}

--div-helper 0 u (a * suc u) u ≡ a
--div-helper div-acc u (n * suc u) j
-- (a * b mod b) {b≢0}   ≡  0


lemModAux′ : ∀ k m b j → mod-helper k m (suc j ℕ.+ b) j ≡ mod-helper 0 m b m
lemModAux′ k m b  zero   = refl
lemModAux′ k m b (suc j) = lemModAux′ (suc k) m b j

modAuxGt : ∀ k a b j → a ℕ.≤ j → mod-helper k b a j ≡ k ℕ.+ a
modAuxGt k  zero   b  j      lt rewrite +-right-identity k = refl 
modAuxGt k (suc a) b zero ()
modAuxGt k (suc a) b (suc j) (s≤s lt) rewrite +-suc k a = modAuxGt (suc k) a b j lt

open import Data.Nat.Divisibility

g : (m b a : ℕ) → {!!}
g m b a = let q = modAuxGt 0 m (b * a) m ≤-refl in {!!}

al : (m b : ℕ) → mod-helper 0 m (suc m * b) m ≡ 0
al m b = {!∣-*!}

kk :  (a k m n j : ℕ) → n ≡ a * m → mod-helper k m n j ≡ 0
kk a k m zero j x = {!!}
kk a k m (suc n) j x = {!!}

mod-a : (k m n j : ℕ) → k ≡ 0 ⊎ n > m ∸ j → mod-helper k m (n * j) j ≡ 0
mod-a k m zero j (inj₁ x) = x
mod-a k m zero j (inj₂ ())
mod-a k m (suc n) j x = {!!}

mod-lemma₃ : (acc d n : ℕ) →
              let s = acc ℕ.+ n in
               acc ≡ 0 ⊎ (d * suc s) > n → 
               mod-helper acc s (d * suc s) n ≡ 0
mod-lemma₃ .0 zero n (inj₁ refl) = refl
mod-lemma₃ acc zero n (inj₂ ())
mod-lemma₃ .0 (suc d) zero (inj₁ refl) = mod-lemma₃ 0 d 0 (inj₁ refl)
mod-lemma₃ zero (suc d) zero (inj₂ (s≤s z≤n)) = mod-lemma₃ 0 d 0 (inj₁ refl)
mod-lemma₃ (suc acc) (suc d) zero (inj₂ (s≤s z≤n)) = {!mod-lemma₃ acc d (acc ℕ.+ 0) ?!}
mod-lemma₃ .0 (suc d) (suc n) (inj₁ refl) = {!mod-lemma₃ 0 (suc d) n!}
mod-lemma₃ acc (suc d) (suc n) (inj₂ y) = {!!} 
{-
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


mod-a k m zero j (inj₁ x) = x
mod-a k m zero j (inj₂ )
mod-a .0 m (suc n) zero (inj₁ refl) = mod-a 0 m n 0 (inj₁ refl)
mod-a k m (suc n) zero (inj₂ (s≤s (s≤s y))) = {!mod-a k m 0 0!}
od-a k m (suc n) (suc j) x = {!mod-a (suc k) m n j ?!}

mod-a m zero j = refl
mod-a m (suc n) zero rewrite *-comm n 1 | +-right-identity n = {!n!}
mod-a m (suc n) (suc j) = {!mod-a (suc m) n j!} -- suc n is een meervoud van j
-}

mod-b : (m n j : ℕ) → mod-helper 1 j (n * suc j) j ≡ 0
mod-b m n j = {!!}

div-a : (a div-acc m n j : ℕ) → n ≡ a * suc m → j ≡ m → div-helper div-acc m n j ≡ a
div-a a div-acc m zero j x x₁ = {!x₁!}
div-a a div-acc m (suc n) j x x₁ = {!!}

div-helper₃ : (n : ℕ) → div-helper 0 0 n 0 ≡ n
div-helper₃ zero = refl
div-helper₃ (suc n) = trans (div-helper₄ 1 n) (cong suc (div-helper₃ n))

div-helper-x : (a u : ℕ) → div-helper 0 u (a * suc u) u ≡ a → div-helper 0 (suc u) (a * suc (suc u)) (suc u) ≡ a
div-helper-x a u x = {!!}

{-
ddd : (a u div-acc mod-add m n j : ℕ)
       n ≡ suc u * ?
       

div-helper 0 u (a * suc u) u   div-acc m n j ≡ a
a*b/b≡a : (a u : ℕ) → {u≢0 : False (u ℕ.≟ 0)} → ((a * u) div u) {u≢0} ≡ a
a*b/b≡a a zero {u≢0} = ⊥-elim u≢0
a*b/b≡a a (suc u) {u≢0} with ∣-* a {u}
a*b/b≡a a (suc u) {u≢0} | divides zero eq = {!!}
a*b/b≡a a (suc u) {u≢0} | divides (suc q) eq = {!eq!}
-}
qqq : (a u : ℕ) → div-helper 0 u (a * suc u) u ≡ a
qqq zero u = refl
qqq (suc a) u = {!u!}


-- o :      k =  div-helper k m n j          k * m + div-helper k m n j ≡ o

d' : (k m n j : ℕ) → j ≡ n → m ≥ n → div-helper k m n j ≡ k
d' k m zero j x x₁ = refl
d' k m (suc n) zero () x₁
d' k .(suc _) (suc n) (suc .n) refl (s≤s x₁) = d' k (suc _) n n refl (≤-step x₁)
{-
d' k m zero j x x₁ = refl
d' k .0 (suc n) zero refl ()
d' k .(suc j) (suc n) (suc j) refl q = {!d'!}
-}
{-
d' a zero .0 j q refl = refl
d' a (suc l) n zero () _
d' a (suc l) n (suc j) q r = {!d' a (suc l) n (suc j) q r!}
-}


qr≡ : (o oa a l k m n j : ℕ)
     → o ≡ oa * m
     → a ℕ.+ k ≡ oa
     → 
     → 
     -- constraint op l, we begonnen ooit bij 0
     -- constraint op k, we begonnen ooit bij 0
     → m ≡ l ℕ.+ j
     → n ≡ a * m
     → j ℕ.≤ m
     → div-helper k m n j ≡ a
qr≡ o oa a l k m zero j x x₁ x₂ x₃ x₄ = {!!}  -- a is 0; of m ≡ 0.
qr≡ o oa a l k m (suc n) zero x x₁ x₂ x₃ x₄ = qr≡ o oa a l (suc k) m n m x {!!} {!!} {!!} {!!}
qr≡ o oa a l k m (suc n) (suc j) x x₁ x₂ x₃ x₄ = {!!}


d≡ : (o oa a l k n j : ℕ) → let m = j ℕ.+ l in
     (a ℕ.+ k) ≡ oa
     → n ≡ a * suc (j ℕ.+  l) → div-helper k (j ℕ.+ l) n j ≡ oa
d≡ o oa zero l k zero j x x₁ = x
d≡ o .(suc (a ℕ.+ k)) (suc a) l k zero j refl ()
d≡ o oa zero l k (suc n) zero x ()
d≡ o .(suc k) (suc zero) l k (suc .(l ℕ.+ 0)) zero refl refl rewrite +-right-identity l = d' (suc k) l l l refl ≤-refl  -- hier nodig dat: ?
d≡ o oa (suc (suc a)) l k (suc n) zero x x₁ = {!d≡ o oa a l (suc k) (suc n) l ? !}
d≡ o oa a l k (suc n) (suc j) x x₁ = {!!}


q≡ : (a b : ℕ) → div-helper 0 b (a * suc b) b ≡ a
q≡ a b = {!d≡ (a * suc b) a a 0 0 (a * suc b) b ? ?!}
 -- subst (λ x → div-helper 0 x (a * suc b) b ≡ a) (+-right-identity b) (d≡ a 0 0 (a * suc b) b (cong (a *_) (cong suc (sym (+-right-identity b)))))
-- (a ℕ.+ div-helper 0 b (a * suc b) b) * suc b  ≡ a * suc b

zz : (a b : ℕ) → div-helper 0 b (a * suc b) b ≡ a
zz zero b = refl
zz (suc a) b = {!!}

open import Agda.Builtin.Unit
a*b/b≡a : (a u : ℕ) → {u≢0 : False (u ℕ.≟ 0)} → ((a * u) div u) {u≢0} ≡ a
a*b/b≡a a zero {()}
a*b/b≡a a (suc u) {u≢0} = q≡ a u

b*a/b≡a : (a u : ℕ) → {u≢0 : False (u ℕ.≟ 0)} → ((u * a) div u) {u≢0} ≡ a
b*a/b≡a a zero {u≢0} = ⊥-elim u≢0
b*a/b≡a a (suc zero) {u≢0} rewrite +-right-identity a = div-helper₃ a
b*a/b≡a a (suc (suc u)) {u≢0} = {!b*a/b≡a a (suc u) {?}!}
--
-- or    *-/-assoc   (a * b) / c  ≡  a * ( b / c)
-- but (2 * 3) / 2   ≢    2 * (3 / 2)       


goal : (a b u : ℕ) → {u≢0 : False (u ℕ.≟ 0)} → a ℕ.≤ b * u → (a div u) {u≢0} ℕ.≤ b
goal a b u {u≢0} x = subst (λ x → (a div u) {u≢0} ℕ.≤ x) (a*b/b≡a b u {u≢0}) (div-mono u {u≢0} x)



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

𝔽×𝔽-to-𝔽 : {n m : ℕ} → (Fin n × Fin m) → Fin (n * m)
𝔽×𝔽-to-𝔽{n} {m} (a , b) = fromℕ≤ {𝔽.toℕ a * 𝔽.toℕ b} {n * m} (≤-trans (s≤s (m≤n⇒m≤k+n {𝔽.toℕ a * 𝔽.toℕ b} {𝔽.toℕ a * suc (𝔽.toℕ b)} (≤-refl {𝔽.toℕ a} *-mono ≤-step ≤-refl) (𝔽.toℕ b))) (bounded a *-mono bounded b))


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


