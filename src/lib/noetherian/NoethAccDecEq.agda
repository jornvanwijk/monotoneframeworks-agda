
module NoethAccDecEq where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Data.List
open import Data.Nat

open import Utilities
open import Noetherian

data Path {X : Set} : {acc : List X} → NoethAcc' X acc → List X → Set where
  stop : ∀{acc}{d : Dup acc} → Path (stop d) []
  ask : ∀{acc xs x}{n : (x : X) → NoethAcc' X (x ∷ acc)}
    → Path (n x) xs → Path (ask n) (x ∷ xs)

isPropPath : {X : Set}{acc xs : List X}{n : NoethAcc' X acc}
  → (p p' : Path n xs) → p ≡ p'
isPropPath stop stop = refl
isPropPath (ask p) (ask p') = cong ask (isPropPath p p')

dupfeedNoeth : {X : Set}{acc xs : List X}(n : NoethAcc' X acc)
  → Path n xs → Dup (acc ++R xs)
dupfeedNoeth (stop d) stop = dup++R d
dupfeedNoeth (ask n) (ask p) = dupfeedNoeth (n _) p

constFeed : {X : Set}{acc : List X} → NoethAcc' X acc → X → List X
constFeed (stop d) x = []
constFeed (ask n) x = x ∷ constFeed (n x) x

constFeedPath : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x : X)
  → Path n (constFeed n x)
constFeedPath (stop d) x = stop
constFeedPath (ask n) x = ask (constFeedPath (n x) x)  

constFeedDup : {X : Set}(n : NoethAcc X)(x : X) → Dup (constFeed n x)
constFeedDup n x = dupfeedNoeth n (constFeedPath n x)

changeFeed' : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x y : X)
  → Dup (constFeed n x) → List X
changeFeed' (stop n) x y ()
changeFeed' (ask n) x y (duphere d) = y ∷ constFeed (n y) x
changeFeed' (ask n) x y (dupthere d) = x ∷ changeFeed' (n x) x y d

changeFeed : {X : Set}(n : NoethAcc X)(x y : X) → List X
changeFeed n x y = changeFeed' n x y (constFeedDup n x)

changeFeedPath : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x y : X)
  → (d : Dup (constFeed n x))
  → Path n (changeFeed' n x y d)
changeFeedPath (stop n) x y ()
changeFeedPath (ask n) x y (duphere d) = ask (constFeedPath (n y) x)
changeFeedPath (ask n) x y (dupthere d) = ask (changeFeedPath (n x) x y d)

changeFeedDup : {X : Set}(n : NoethAcc X)(x y : X) → Dup (changeFeed n x y)
changeFeedDup n x y = dupfeedNoeth n (changeFeedPath n x y _)

∈constFeed : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x y : X)
  → y ∈ constFeed n x → x ≡ y
∈constFeed (stop d) x y ()
∈constFeed (ask n) x .x (here refl) = refl
∈constFeed (ask n) x y (there p) = ∈constFeed (n x) x y p  

dupDecEq : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x y : X)
  → (d : Dup (constFeed n x))
  → (d' : Dup (changeFeed' n x y d))
  → lengthDup d ≡ lengthDup d' → x ≡ y
dupDecEq (stop n) x y () d' eq
dupDecEq (ask n) x y (duphere d) (duphere d') eq = ∈constFeed (n y) x y d'
dupDecEq (ask n) x y (duphere d) (dupthere d') ()
dupDecEq (ask n) x y (dupthere d) (duphere x₁) ()
dupDecEq (ask n) x y (dupthere d) (dupthere d') eq =
  dupDecEq (n x) x y d d' (sucInj eq)

changeFeedEq : {X : Set}{acc : List X}(n : NoethAcc' X acc)(x : X)
  → (d : Dup (constFeed n x))
  → constFeed n x ≡ changeFeed' n x x d
changeFeedEq (stop n) x ()
changeFeedEq (ask n) x (duphere d) = refl
changeFeedEq (ask n) x (dupthere d) = cong (_∷_ x) (changeFeedEq (n x) x d)

dupDecEq2 : {X : Set}(n : NoethAcc X)(x y : X) → x ≡ y
  → lengthDup (constFeedDup n x) ≡ lengthDup (changeFeedDup n x y)
dupDecEq2 n x .x refl =
  cong₂-dep (λ a b → lengthDup (dupfeedNoeth {xs = a} n b)) (changeFeedEq n x _)
    (isPropPath _ _)
  where
    cong₂-dep : {X : Set}{Y : X → Set}{Z : Set}(f : (x : X) → Y x → Z)
      → {x x' : X}{y : Y x}{y' : Y x'}
      → (eq : x ≡ x') → subst Y eq y ≡ y' → f x y ≡ f x' y'
    cong₂-dep f refl refl = refl  

NoethDecEq : {X : Set} → NoethAcc X → DecEq X
NoethDecEq n x y with
  lengthDup (constFeedDup n x) ≟ lengthDup (changeFeedDup n x y)
NoethDecEq n x y | yes eq = yes (dupDecEq n x y _ _ eq)
NoethDecEq n x y | no ¬eq = no (λ eq → ¬eq (dupDecEq2 n x y eq))
