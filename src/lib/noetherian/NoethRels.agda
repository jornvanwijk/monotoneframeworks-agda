

module NoethRels where

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
open import Data.Nat.Properties.Simple

open import Noetherian

{- NoethAcc→NoethAccS -}

¬DupCons : {X : Set} {acc : List X} {x : X}
  → ¬ Dup acc → ¬ x ∈ acc → ¬ Dup (x ∷ acc)
¬DupCons ¬d ¬m (duphere m) = ¬m m
¬DupCons ¬d ¬m (dupthere d) = ¬d d  

NoethAcc'→NoethAccS' : {X : Set} (acc : List X) → ¬ Dup acc
  → NoethAcc' X acc → NoethAccS' X acc
NoethAcc'→NoethAccS' acc ¬d (stop d) = ⊥-elim (¬d d)
NoethAcc'→NoethAccS' acc ¬d (ask n) =
  ask (λ x ¬m → NoethAcc'→NoethAccS' (x ∷ acc) (¬DupCons ¬d ¬m) (n x))

NoethAcc→NoethAccS : {X : Set} → NoethAcc X → NoethAccS X
NoethAcc→NoethAccS n = NoethAcc'→NoethAccS' [] (λ ()) n



{- NoethAccS→NoethSet: this direction require function extentionality so we put
   it in a separate module -}

module NoethAccS→Noet
  (funext : {X Y : Set} {f g : X → Y} → (∀ x → f x ≡ g x) → f ≡ g) where

  proj₁≡ : {X : Set}{Y : X → Set}{xy xy' : Σ[ x ∈ X ] Y x}
    → xy ≡ xy' → proj₁ xy ≡ proj₁ xy'
  proj₁≡ refl = refl

  Σ≡ : {X : Set}{Y : X → Set}{xy xy' : Σ[ x ∈ X ] Y x}
    → (∀ x → isProp (Y x))
    → proj₁ xy ≡ proj₁ xy' → xy ≡ xy'
  Σ≡ p refl = cong (_,_ _) (p _)


  Inj : {A B : Set}(f : A → B) → Set
  Inj {A}{B} f = {a a' : A} → f a ≡ f a' → a ≡ a'

  Surj : {X Y : Set}(f : X → Y) → Set
  Surj {X}{Y} f = Σ[ g ∈ (Y → X) ] ((y : Y) → f (g y) ≡ y)



  ¬isProp : {X : Set} → isProp (¬ X)
  ¬isProp {X}{¬x} = funext (λ x → ⊥-elim (¬x x))

  NoethAccS→NoethSet' : {X X' : Set} (acc : List X)
    → (f : X' → X) → (∀ x' → ¬ f x' ∈ acc) → Inj f
    → NoethAccS' X acc → NoethSet X'
  NoethAccS→NoethSet' acc f p i (ask n) = 
    ask (λ x' → NoethAccS→NoethSet' (f x' ∷ acc) 
      (λ {(y' , ¬eq) → f y'})
        (λ { (y' , ¬i) (here eq) → ¬i (i (sym eq)) ;
             (y' , _) (there q) → p y' q })
      (λ { {z , q}{z' , q'} eq → Σ≡ (λ _ → ¬isProp) (i eq)})
      (n (f x') (p x')))

  NoethAccS→NoethSet : {X : Set} → NoethAccS X → NoethSet X
  NoethAccS→NoethSet n = NoethAccS→NoethSet' [] id (λ {_ () }) id n


{- NoethSet→NoethAccS -}

mutual
 MinList : (X : Set)(acc : List X) → (Dup acc → ⊥) → Set
 MinList X [] _ = X
 MinList X (x ∷ acc) nd = (MinList X acc (λ z → nd (dupthere z))) ⧹ dd X acc x (λ z → nd (dupthere z)) (λ z → nd (duphere z))

 dd : (X : Set)(acc : List X) → (x : X) → (nd : Dup acc → ⊥) → (x ∈ acc → ⊥) → MinList X acc nd
 dd X [] x nd xi = x
 dd X (x ∷ acc) x₁ nd xi = dd X acc x₁ (λ z → nd (dupthere z)) (λ xi' → xi (there xi')) , (λ eq → xi (subst (λ a → a ∈ x ∷ acc) (dd-lem X acc x x₁ (λ d → nd (dupthere d)) _ _ eq) (here  refl)))

 dd-lem : (X : Set)(acc : List X) → (x x' : X) → (nd : Dup acc → ⊥) → (ix : x ∈ acc → ⊥) → (ix' : x' ∈ acc → ⊥) 
    → dd X acc x nd ix ≡ dd X acc x' nd ix' → x ≡ x'
 dd-lem X [] x x' nd ix id' eq = eq
 dd-lem X (x ∷ acc) x₁ x' nd ix id' eq = dd-lem X acc _ _ _ _ _ (cong proj₁ eq)


NoethSet→NoethAccS' : {X : Set} (acc : List X) → (nd : Dup acc → ⊥)
  → NoethSet (MinList X acc nd) → NoethAccS' X acc
NoethSet→NoethAccS' {X} acc nd (ask n) = ask (λ x xi → NoethSet→NoethAccS' (x ∷ acc) (λ { (duphere x₁) → xi x₁ ; (dupthere d) → nd d } ) (n (dd X acc x nd xi) ) )


NoethSet→NoethAccS : {X : Set} → NoethSet X → NoethAccS X 
NoethSet→NoethAccS ns = NoethSet→NoethAccS' [] (λ ()) ns

{- NoethAccS→NoethGame  -}

NoethAccS→NoethGame' : {X : Set}(acc : List X)
  → NoethAccS' X acc → NoethGame' X acc
NoethAccS→NoethGame' acc (ask n) = ask (λ x p → NoethAccS→NoethGame' _ (n x p))

NoethAccS→NoethGame : {X : Set} → NoethAccS X → NoethGame X
NoethAccS→NoethGame = NoethAccS→NoethGame' [] 

{- NoethExpose→Listable -}
open import Listable

NoethExpose→Listable' : {X : Set} → (acc : List X) → X → NoethExpose' X acc → Listable X
NoethExpose→Listable' acc x (stop x₁) = acc , x₁
NoethExpose→Listable' acc x (tell x'' n) = NoethExpose→Listable' (x'' ∷ acc) x'' n
NoethExpose→Listable' acc x (ask x₁) = NoethExpose→Listable' (x ∷ acc) x (x₁ x)

NoethExpose→Listable : {X : Set} → X → NoethExpose X → Listable X
NoethExpose→Listable = NoethExpose→Listable' []
