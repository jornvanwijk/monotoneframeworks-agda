
module StreamlessProps where


open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
open import Data.Colist renaming (_∈_ to _∈c_)
open import Utilities
open import Coinduction
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Empty

open import Noetherian
open import Streamless


{- NoethAcc→Streamless  -} 

DupS++ : ∀{X}{xs}(ys : List X) → DupS xs → DupS (ys S++ xs)
DupS++ [] p = p
DupS++ (x ∷ ys) p = DupS++ ys (dupthere p)

∈S∼ : {X : Set}{xs ys : Stream X}(p : xs ∼ ys){x : X} → x ∈S xs → x ∈S ys
∈S∼ (∷∼ p) here = here
∈S∼ (∷∼ p) (there q) = there (∈S∼ (♭ p) q)

DupS∼ : {X : Set}{xs ys : Stream X}(p : xs ∼ ys) → DupS xs → DupS ys
DupS∼ (∷∼ p) (duphere d) = duphere (∈S∼ (♭ p) d)
DupS∼ (∷∼ p) (dupthere d) = dupthere (DupS∼ (♭ p) d)

S++∷ : ∀{X}{xs}(ys : List X){x : X} → ((x ∷ ys) S++ (♭ xs)) ∼ (ys S++ (x ∷ xs))
S++∷ ys = S++∼ ys (∷∼ (♯ refl∼))

Dup→Dup++S'' : ∀{X}{xs}(ys : List X) → DupS xs → DupS (ys S++ xs)
Dup→Dup++S'' [] d = d
Dup→Dup++S'' (x ∷ ys) d = Dup→Dup++S'' ys (dupthere d)

Dup→Dup++S' : ∀{X}{xs}{ys : List X}{x : X} → x ∈ ys → x ∈S xs →
              DupS (ys S++ xs)
Dup→Dup++S' {ys = x ∷ ys} (here refl) q = Dup→Dup++S'' ys (duphere q)
Dup→Dup++S' (there p) q = Dup→Dup++S' p (there q)

Dup→Dup++S : ∀{X}{xs}{ys : List X} → Dup ys → DupS (ys S++ xs)
Dup→Dup++S {ys = x ∷ ys} (duphere p) = Dup→Dup++S' p here
Dup→Dup++S (dupthere p) = Dup→Dup++S p


NoethAcc→Streamless' : {X : Set}(acc : List X)(xs ys : Stream X) →
                   NoethAcc' X acc → (acc S++ xs) ∼ ys → DupS ys
NoethAcc→Streamless' acc (x ∷ xs) ys (stop d) p = DupS∼ p (Dup→Dup++S d)
NoethAcc→Streamless' acc (x ∷ xs) ys (ask n) p = NoethAcc→Streamless' (x ∷ acc) (♭ xs) ys 
  (n x) (trans∼ (S++∼ acc (∷∼ (♯ refl∼))) p)


NoethAcc→Streamless : {X : Set} → NoethAcc X → Streamless X
NoethAcc→Streamless n xs = NoethAcc→Streamless' [] xs xs n refl∼


{- NoethAccS→StreamlessS -}

NoethAccS→StreamlessS' : {X : Set} → (acc : List X) → NoethAccS' X acc → (Dup acc → ⊥)  
  → (xs : Colist X) 
  → (∀ x → x ∈c xs → x ∈ acc → ⊥)
  → ¬ DupC xs → Finite xs
NoethAccS→StreamlessS' acc (ask x) d [] zz dup = []
NoethAccS→StreamlessS' acc (ask x) d (x₁ ∷ xs) zz dup = x₁  ∷ helper
  where
   helper : Finite (♭ xs)
   helper = NoethAccS→StreamlessS' (x₁ ∷ acc) (x x₁ (λ x1i → zz x₁ (here refl) x1i)) 
     (λ { (duphere x₂) → zz x₁ (here refl) x₂ ; (dupthere dupc) → d dupc } ) (♭ xs) 
       (λ { x2 x2i (here x₂) → dup 
          (subst (λ a → DupC (a ∷ xs)) x₂ (duphere x2i)) ; 
            x2 x2i (there x2i') → zz x2  (there x2i) x2i' }) 
            (λ dupc → dup (dupthere dupc))


NoethAccS→StreamlessS : {X : Set} → (acc : List X) → NoethAccS X → StreamlessS X
NoethAccS→StreamlessS acc n  xs nd = NoethAccS→StreamlessS' [] n (λ ()) xs (λ x _ → λ ()) nd
