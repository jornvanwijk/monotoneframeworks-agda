
open import Relation.Binary.PropositionalEquality

module NotNotIn (funext : {X Y : Set} {f g : X → Y} → (∀ x → f x ≡ g x) → f ≡ g) where

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


NotNotIn : {X : Set} → List X → Set
NotNotIn {X} xs = Σ[ x ∈ X ] ¬ ¬ x ∈ xs


fin-noeth-2 : {X : Set} 
  → (xs : List X)
  → (acc : List X) → ¬ Dup acc 
  → (∀ x → x ∈ acc → ¬ ¬ x ∈ xs)
  → ¬ ¬ length acc ≤ length xs 
fin-noeth-2 xs [] ¬dup f ¬l = ¬l z≤n
fin-noeth-2 xs (x ∷ acc) ¬dup f ¬l with f x (here refl)
fin-noeth-2 [] (x ∷ acc) ¬dup f ¬l | p = p (λ { () })
fin-noeth-2 (x ∷ xs) (x' ∷ acc) ¬dup f ¬l | r = r (λ p → ¬l (⊥-elim (fin-noeth-2 (remove (x ∷ xs) p) acc (λ d → ¬dup (dupthere d))
  (λ y q ¬m → f y (there q) (λ r' → ¬m (∈remove (λ eq → ¬dup (duphere (subst (λ z → z ∈ acc) eq q))) p r'))) (λ c → ¬l (s≤s (subst (_≤_ _) (length-remove p refl) c))))))


  
¬¬isProp : {X : Set} → isProp (¬ ¬ X)
¬¬isProp {X}{¬¬x} = funext (λ ¬x → ⊥-elim (¬¬x ¬x))

∈prop : {X : Set}{P : X → Set}(isprop : (x : X) → isProp (P x))(xs : List (Σ X P))
        {x : X}{p : P x} → x ∈ map proj₁ xs → (x , p) ∈ xs
∈prop isprop [] ()
∈prop isprop ((x , p) ∷ xs) (here refl) = here (cong (_,_ x) (isprop x))
∈prop isprop (x ∷ xs) (there m) = there (∈prop isprop xs m)        

∈prop-2 : {X : Set}{P : X → Set}(xs : List (Σ X P))
          {x : X} → x ∈ map proj₁ xs → P x
∈prop-2 [] ()
∈prop-2 ((x , p) ∷ xs) (here refl) = p
∈prop-2 (x ∷ xs) (there m) = ∈prop-2 xs m

dupprop : {X : Set}{P : X → Set}(isprop : (x : X) → isProp (P x))(xs : List (Σ X P)) →
          Dup (map proj₁ xs) → Dup xs
dupprop isprop [] ()
dupprop isprop ((x , p) ∷ xs) (duphere m) = duphere (∈prop isprop xs m)
dupprop isprop (x ∷ xs) (dupthere d) = dupthere (dupprop isprop xs d)        

length-lem : {X : Set} (xs : List X){x : X} → length (x ∷ xs) ≤ length xs → ⊥
length-lem [] ()
length-lem (x ∷ xs) (s≤s le) = length-lem  xs {x} le                         

length-map : {X Y : Set}{f : X → Y} (xs : List X) → length xs ≡ length (map f xs) 
length-map [] = refl
length-map (x ∷ xs) = cong suc (length-map xs)

fin-noeth-1 : {X : Set} → (xs : List X) → (n : ℕ)
  → (acc : List (NotNotIn xs)) → (n +N length acc ≡ length xs) → ¬ Dup acc  → NoethAccS' (NotNotIn xs) acc
fin-noeth-1 xs zero acc ind ¬dup =
  ask (λ { (x' , ¬¬m) xia → ⊥-elim (fin-noeth-2 xs (x' ∷ map proj₁ acc)
    (λ { (duphere d) → xia (∈prop (λ _ → ¬¬isProp) acc d) ; (dupthere d) → ¬dup (dupprop (λ _ → ¬¬isProp) acc d) })
    (λ { ._ (here refl) → ¬¬m ; x (there m) → ∈prop-2 acc m }) (λ l → length-lem (map proj₁ acc) {x'} (subst (_≤_ _) (trans (sym ind) (length-map acc)) l))) } )
fin-noeth-1 xs (suc n) acc ind ¬dup = ask (λ x' xia → fin-noeth-1 xs n (x' ∷ acc) (trans (+-suc n (length acc)) ind) (λ { (duphere d) → xia d ; (dupthere d) → ¬dup d }))


NoethAccSNotNotIn : {X : Set} → (xs : List X) → NoethAccS (NotNotIn xs)
NoethAccSNotNotIn xs = fin-noeth-1 xs (length xs) [] (+-right-identity _) (λ { () })


EqNotNotIn→Eq : ((X : Set) (xs : List X) → DecEq (NotNotIn xs))
  → (X : Set) → DecEq X
EqNotNotIn→Eq dec X x y with dec X (x ∷ y ∷ []) (x , (λ z → z (here refl))) (y , (λ z → z (there (here refl))))
EqNotNotIn→Eq dec X x y | yes p = yes (cong proj₁ p)
EqNotNotIn→Eq dec X x y | no ¬p = no (λ r → h x y _ _  r ¬p ¬¬isProp)
  where
   h : {X : Set}{Y : X → Set}  → (x y : X) → (q : Y x) → (p : Y y) → (eq : x ≡ y) 
                              → ¬ (x , q) ≡ (y , p) → subst (λ h → Y h) eq q ≡ p →  ⊥
   h x₁ .x₁ q p refl neq seq = neq (cong (λ p → (x₁ , p)) seq)

