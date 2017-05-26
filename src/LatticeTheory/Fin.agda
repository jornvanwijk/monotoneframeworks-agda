import Level
open import Data.Nat renaming (_⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≟_ to _ℕ≟_)

module LatticeTheory.Fin where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Unit hiding (_≟_ ; ⊤)
open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Fin
open import Data.Fin.Properties
open import LatticeTheory.Unit
open import Relation.Binary
open import Data.Nat.Properties
open import Function.Injection



-- inject≤ : ∀ {m n} → Fin m → m N≤ n → Fin n
Finᴸ′ : (n : ℕ) → BoundedSemiLattice Level.zero
Finᴸ′ n = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set 
  ℂ = Fin (suc n)
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  ⊥ : ℂ 
  ⊥ = zero
  ⊤ : ℂ
  ⊤ = fromℕ≤ {n} {suc n} (s≤s (≤′⇒≤ ≤′-refl))
  _⊔_ : Op₂ ℂ
  x ⊔ y with x Data.Fin.≤? y
  x ⊔ y | yes p = y
  x ⊔ y | no ¬p = x
{-
  x ⊔ y with toℕ x Data.Nat.+ toℕ y Data.Nat.≤? n
  x ⊔ y | yes p = fromℕ≤ (s≤s p) -- inject≤ {toℕ x Data.Nat.+ toℕ y} {suc n} {!x Data.Fin.+ y!} {!p!} --inject≤ (x Data.Fin.+ y) p
  x ⊔ y | no ¬p = ⊤ -- new number:  (x + y) - (x + y - n)
  -}
  _⊓_ : Op₂ ℂ
  x ⊓ y with x Data.Fin.≤? y
  x ⊓ y | yes p = x
  x ⊓ y | no ¬p = y

  _≟′_ : Decidable {A = ℂ} _≡_
  x ≟′ y = Data.Fin.Properties.eq? Function.Injection.id x y
  
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal c = refl

  ⊤-isMaximal : (c : ℂ) → c ⊑ ⊤
  ⊤-isMaximal zero = refl
  ⊤-isMaximal (suc c) with suc (toℕ c) Data.Nat.≤? toℕ (fromℕ≤ (s≤s {!!}))
  ⊤-isMaximal (suc c) | yes p = {!!}
  ⊤-isMaximal (suc c) | no ¬p = {!!} 
  ⊔-idem : Idempotent _⊔_
  ⊔-idem x with x Data.Fin.≤? x
  ⊔-idem x | yes p = refl
  ⊔-idem x | no ¬p = refl
  ⊔-comm : Commutative _⊔_
  ⊔-comm x y with x Data.Fin.≤? y | y Data.Fin.≤? x
  ⊔-comm x y | yes p | (yes p₁) = {!!}
  ⊔-comm x y | yes p | (no ¬p) = refl
  ⊔-comm x y | no ¬p | (yes p) = refl
  ⊔-comm x y | no ¬p | (no ¬p₁) = {!!}
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = {!!}
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = {!!}
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = {!!}

open import Relation.Unary

{-

x+y  >  n ?    dan       n
               anders    x + y



     min (x + y) n    -    max (x + y) n

     n - (x + y)


-}


open import Util.Product
-- inject≤ : ∀ {m n} → Fin m → m N≤ n → Fin n
record Bounded (n : ℕ) : Set where
  constructor _≤-by_ 
  field
    m : ℕ
    m≤n : m Data.Nat.≤ n

Fin-predᴸ : (n : ℕ) → BoundedSemiLattice Level.zero
Fin-predᴸ n = completeLattice ℂ _⊔_ _≟′_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set Level.zero
  ℂ = Bounded n
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  ⊥ : ℂ 
  ⊥ = zero ≤-by z≤n
  ⊤ : ℂ
  ⊤ = n ≤-by ≤′⇒≤ ≤′-refl 
  _⊔_ : Op₂ ℂ
  (x ≤-by x≤n) ⊔ (y ≤-by y≤n)  with x Data.Nat.+ y Data.Nat.≤? n
  (x ≤-by x≤n) ⊔ (y ≤-by y≤n) | yes p = (x Data.Nat.+ y) ≤-by p
  (x ≤-by x≤n) ⊔ (y ≤-by y≤n) | no ¬p = ⊤
  _⊓_ : Op₂ ℂ
  x ⊓ y  = {!!}
  
  _≟′_ : Relation.Binary.Decidable {A = ℂ} _≡_
  x ≟′ y = {!Data.Fin.Properties.eq?!}
  open Operators ℂ ⊥ _⊔_ _≟′_ --_≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal (m ≤-by m≤n) with m Data.Nat.≤? n
  ⊥-isMinimal (m ≤-by m≤n) | yes p = {!!}
  ⊥-isMinimal (m ≤-by m≤n) | no ¬p = {!!} 
  ⊔-idem : Idempotent _⊔_
  ⊔-idem = {!!}
  ⊔-comm : Commutative _⊔_
  ⊔-comm = {!!}
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = {!!}
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = {!!}
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = {!!}









liftF : (n : ℕ) → (Fin n) → (Fin (suc n))
liftF zero ()
liftF (suc n) zero = zero
liftF (suc n) (suc x) = suc (liftF n x)


lemma : (l : ℕ) →  (n m : Fin l) -> m Data.Fin.< n -> ((liftF l m) Data.Fin.< suc n)
lemma zero () m x
lemma (suc l) zero zero ()
lemma (suc l) zero (suc m) ()
lemma (suc l) (suc n) zero (s≤s z≤n) = s≤s z≤n
lemma (suc l) (suc n) (suc m) (s≤s x) = s≤s (lemma l n m x)

lemma₂ : (n : ℕ) → (x : Fin n) -> Acc Data.Fin._<_ x -> Acc Data.Fin._<_ (liftF (suc n) (suc x))
lemma₂ zero () x₁
lemma₂ (suc n) zero (acc rs) = acc (λ{ zero (s≤s z≤n) → acc (λ{ y ()}) ; (suc y) (s≤s ())})
lemma₂ (suc n) (suc x) (acc rs) = acc (λ{ y (s≤s x₁) → ⊥-elim {!lemma₂ n x !}})  -- something like, eventually we reach 0, but zero has no predecessor.

{-
from Data.Nat.Properties:
-- Converting between ≤ and ≤′

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ ≤′-refl        = ≤-refl
≤′⇒≤ (≤′-step m≤′n) = ≤-step (≤′⇒≤ m≤′n)

z≤′n : ∀ {n} → zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

-}
finwf : (n : ℕ) → (x : Fin n) → Acc Data.Fin._<_ x
finwf zero ()
finwf (suc n) zero = acc (λ{ y ()})
finwf (suc n) (suc x) = acc (λ{ y z → {!finwf n!}})  -- stel dat x is accessible, dan is suc x ook accessible, want alles wat kleiner dan suc x is, is x, en alles dat transitief kleiner dan x is.

open import Induction.Nat

g : {!!}
g = {!<-well-founded on toℕ!}
myBoundedSemiLattice : (m : ℕ) → BoundedSemiLattice Level.zero
myBoundedSemiLattice m = completeLattice {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} --ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : (n : ℕ) → Set Level.zero    
  ℂ n = Fin (suc n)
  --open Algebra.FunctionProperties {A = (ℂ m)} _≡_ 
  _⊔_ : (n : ℕ) → (ℂ n) → (ℂ n) → (ℂ n)
  _⊔_ zero zero zero = zero
  _⊔_ zero zero (suc ())
  _⊔_ zero (suc ()) _ 
  _⊔_ (suc n) zero y = zero
  _⊔_ (suc n) (suc x) zero = zero
  _⊔_ (suc n) (suc a) (suc b) = suc (_⊔_ n a b)
  ⊥ : (n : ℕ) → (ℂ n) 
  ⊥ zero = zero
  ⊥ (suc n) = suc (⊥ n)
  ⊥-isMinimal : (n : ℕ) → (open Operators (ℂ n) (⊥ n) (_⊔_ n) (_≟_)) -> (c : (ℂ n)) -> (⊥ n) ⊑ c
  ⊥-isMinimal zero zero = refl
  ⊥-isMinimal zero (suc ())
  ⊥-isMinimal (suc n) zero = refl
  ⊥-isMinimal (suc n) (suc c) = cong suc (⊥-isMinimal n c)

  open import Induction.Nat

  lemmab : (n : ℕ) → (x y : Fin (suc n)) → (Operators._⊐_ (ℂ n) (⊥ n) (_⊔_ n) (_≟_)) x y → x Data.Fin.≤ y
  lemmab n zero y (proj₁ , proj₂) = z≤n
  lemmab n (suc x) zero (proj₁ , proj₂) = {!!}
  lemmab n (suc x) (suc y) (proj₁ , proj₂) = {!!}

  lemmao : (n : ℕ) -> (x : Fin (suc n)) → Acc _<′_ (toℕ x) → Acc (Operators._⊐_ (ℂ n) (⊥ n) (_⊔_ n) (_≟_)) x
  lemmao n x (acc rs) = acc po
   where po : WfRec ((ℂ n Operators.⊐ ⊥ n) (_⊔_ n) _≟_) (Acc ((ℂ n Operators.⊐ ⊥ n) (_⊔_ n) _≟_)) x
         po y (a , b) with toℕ y Data.Nat.≤? toℕ x
         po y (a , b) | yes p = lemmao n y {!fromℕ≤!}
         po y (a , b) | no ¬p = {!!}

  ⊐-isWellFounded : (n : ℕ) → Well-founded (Operators._⊐_ (ℂ n) (⊥ n) (_⊔_ n) (_≟_))
  ⊐-isWellFounded n x = lemmao n x (<-well-founded (toℕ x))
    where l : (m : ℕ) → (z : ℂ m) → WfRec (Operators._⊐_ (ℂ m) (⊥ m) (_⊔_ m) _≟_) (Acc (Operators._⊐_ (ℂ m) (⊥ m) (_⊔_ m) _≟_)) z
          l m y z p with <-well-founded (toℕ y)
          l m₁ y z p | acc rs = {!!}
{-
          l zero zero zero (a , b) = ⊥-elim (b a)
          l zero zero (suc ()) x₁
          l zero (suc ()) y x₁
          l (suc m₁) zero y (a , b) = ⊥-elim (b a)
          l (suc m₁) (suc z) zero (a , b) with ⊐-isWellFounded m₁ z
          l (suc m₁) (suc z) zero (refl , b) | acc rs = {!!}  -- hier bewijzen dat alles kleiner dan z is well founded,  
          l (suc m₁) (suc z) (suc y) (a , b) = {!!}

-}
 -- alles kleiner dan z is well founded.
 -- z is kleiner dan suc z.
 -- Alles kleiner dan z is well founded, z is kleiner dan suc z. 

  {-
  ⊐-isWellFounded zero zero = acc (λ{ zero (a , b) → ⊥-elim (b a) ; (suc ()) x })
  ⊐-isWellFounded zero (suc ())
  ⊐-isWellFounded (suc n) zero = acc l
    where l : WfRec ((ℂ (suc n) Operators.⊐ _⊔_ (suc n)) _≟_) (Acc ((ℂ (suc n) Operators.⊐ _⊔_ (suc n)) _≟_)) zero
          l zero (a , b) = ⊥-elim (b a)
          l (suc y) (a , b) with ⊐-isWellFounded n y
          l (suc y) (a , b) | acc rs = ⊥-elim (b a)
    
  ⊐-isWellFounded n (suc x) = acc ({!!}) 
    where l : (m : ℕ) → WfRec ((ℂ n Operators.⊐ _⊔_ n) _≟_) (Acc ((ℂ n Operators.⊐ _⊔_ n) _≟_)) (suc x) --WfRec ((ℂ (suc n) Operators.⊐ _⊔_ (suc n)) _≟_) (Acc ((ℂ (suc n) Operators.⊐ _⊔_ (suc n)) _≟_)) (suc x)
          l = {!!}



-}
          {-l n (zero {m}) (refl , b) with ⊐-isWellFounded n x
          l n (zero {.(suc _)}) (refl , b) | acc rs = {!!} -- maybe we need l : {n} → WfRec ..  for zero
          l n (suc y) (a , b) with ⊐-isWellFounded n x
          l n (suc y) (a , b) | acc rs = {!rs y!} -- y is groter dan x
-}
{-
  ⊔-idem : (n : ℕ) → (open Algebra.FunctionProperties {A = (ℂ n)} _≡_) -> (Idempotent (_⊔_ n)
  ⊔-idem = {!!}
  ⊔-comm : (n : ℕ) → (open Algebra.FunctionProperties {A = (ℂ n)} _≡_) -> Commutative (_⊔_ m)
  ⊔-comm = {!!}
  ⊔-cong : (n : ℕ) → (open Algebra.FunctionProperties {A = (ℂ n)} _≡_) -> (_⊔_ m) Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = {!!}
  ⊔-assoc : (n : ℕ) → (open Algebra.FunctionProperties {A = (ℂ n)} _≡_) -> Associative (_⊔_ m)
  ⊔-assoc = {!!}
  ⊐-isWellFounded : (n : ℕ) → Well-founded _⊐_
  ⊐-isWellFounded x = {!!}
 -}

{-
data Fin' : ℕ → Set where
  zero : ∀{n} → Fin' n
  suc  : {n : ℕ} (i : Fin' n) → Fin' (suc n)

_≟f_ : {n : ℕ} → Decidable {A = Fin' n} _≡_
_≟f_ {zero} zero zero = yes refl
_≟f_ {suc n} zero zero = yes refl
_≟f_ {suc n} zero (suc y) = no (λ{ ()})
_≟f_ {suc n} (suc x) zero = no (λ{ ()})
_≟f_ {suc n} (suc x) (suc y) with _≟f_ {n} x y
_≟f_ {suc n} (suc x) (suc y) | yes p = yes (cong suc p)
_≟f_ {suc n} (suc x) (suc y) | no ¬p = no (λ x₁ → ¬p {!!})
-}
open Algebra.FunctionProperties 
_⊔_ : ∀{n} → Op₂ (Fin n)
zero ⊔ b = b
a ⊔ zero = a
suc a ⊔ suc b = suc (a ⊔ b)


{-# TERMINATING #-}
helper : (n : ℕ) → BoundedSemiLattice Level.zero
BoundedSemiLattice.ℂ (helper n) = Fin (suc n)
BoundedSemiLattice._⊔_ (helper zero) = λ{ zero zero → zero ; zero (suc ()) ; (suc ()) y}
BoundedSemiLattice._⊔_ (helper (suc n)) = λ{ zero y → zero ; (suc x) zero → zero ; (suc x) (suc y) → suc (BoundedSemiLattice._⊔_ (helper n) x y)}
BoundedSemiLattice._≟_ (helper n) = _≟_
BoundedSemiLattice.⊥ (helper zero) = zero
BoundedSemiLattice.⊥ (helper (suc n)) = suc (BoundedSemiLattice.⊥ (helper n))
BoundedSemiLattice.⊥-isMinimal (helper zero) = λ{ zero → refl ; (suc ())}
BoundedSemiLattice.⊥-isMinimal (helper (suc n)) zero = refl
BoundedSemiLattice.⊥-isMinimal (helper (suc n)) (suc c) = cong suc (BoundedSemiLattice.⊥-isMinimal (helper n) c)
BoundedSemiLattice.⊔-idem (helper zero) = λ{ zero → refl ; (suc ())}
BoundedSemiLattice.⊔-idem (helper (suc n)) zero = refl 
BoundedSemiLattice.⊔-idem (helper (suc n)) (suc x) = cong suc (BoundedSemiLattice.⊔-idem (helper n) x)
BoundedSemiLattice.⊔-comm (helper zero) = λ{ zero zero → refl ; zero (suc ()) ; (suc ()) y}
BoundedSemiLattice.⊔-comm (helper (suc n)) zero zero = refl
BoundedSemiLattice.⊔-comm (helper (suc n)) zero (suc y) = refl 
BoundedSemiLattice.⊔-comm (helper (suc n)) (suc x) zero = refl 
BoundedSemiLattice.⊔-comm (helper (suc n)) (suc x) (suc y) = cong suc (BoundedSemiLattice.⊔-comm (helper n) x y)
BoundedSemiLattice.⊔-cong₂ (helper n) = λ{ refl refl → refl}
BoundedSemiLattice.⊔-assoc (helper zero) = λ{ zero zero zero → refl ; zero zero (suc ()) ; zero (suc ()) z ; (suc ()) y z}
BoundedSemiLattice.⊔-assoc (helper (suc n)) zero y z = refl
BoundedSemiLattice.⊔-assoc (helper (suc n)) (suc x) zero z = refl
BoundedSemiLattice.⊔-assoc (helper (suc n)) (suc x) (suc y) zero = refl
BoundedSemiLattice.⊔-assoc (helper (suc n)) (suc x) (suc y) (suc z) = cong suc (BoundedSemiLattice.⊔-assoc (helper n) x y z)
BoundedSemiLattice.⊐-isWellFounded (helper zero) zero = acc (λ{ zero (a , b) → ⊥-elim (b a) ; (suc ()) x})
BoundedSemiLattice.⊐-isWellFounded (helper zero) (suc ())
BoundedSemiLattice.⊐-isWellFounded (helper (suc n)) = {!⊐-isWellFounded!}

Finᴸ : (n : ℕ) → BoundedSemiLattice Level.zero
Finᴸ zero = Unitᴸ
Finᴸ (suc n) = helper n

{-
open BoundedSemiLattice (Finᴸ 2)

f : zero ⊑ zero
f = refl

g : zero ⊐ (suc zero)  -- wrong order
g = refl , (λ{ ()})


q : zero Data.Fin.< (suc zero)
q = s≤s z≤n
-}



