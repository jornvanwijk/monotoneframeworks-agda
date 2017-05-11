import Level

module LatticeTheory.TotalFunctionSpace-novec {a : Level.Level} where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Unit hiding (_≟_)
open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Util.Listable
open import Data.List
open import Data.List.All renaming (all to all?)
open import Data.List.All.Properties
open import Util.List.All.Properties

postulate
  fun-ext : ∀{a b} → Extensionality a b
myBoundedSemiLattice : ∀{a b} → (A : Set a) → Listable A → (L : BoundedSemiLattice b) → BoundedSemiLattice (a Level.⊔ b)
myBoundedSemiLattice {a} {b} A ls L = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  ℂ : Set (a Level.⊔ b)
  ℂ = A → L.ℂ
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  (f ⊔ g) x = f x L.⊔ g x
  _≟_ : Decidable {A = ℂ} _≡_
  f ≟ g with all? (λ x → f x L.≟ g x) (Listable.all ls)
  f ≟ g | yes p = yes (fun-ext (λ x → lookup p (Listable.complete ls x)))
  f ≟ g | no ¬p = no (λ x → ¬p (tabulate (λ {y} p → cong (_$ y) x ))) 
  ⊥ : ℂ 
  ⊥ x = L.⊥
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal f = fun-ext (λ x → L.⊥-isMinimal (f x))
  ⊔-idem : Idempotent _⊔_
  ⊔-idem f = fun-ext (λ x → L.⊔-idem (f x))
  ⊔-comm : Commutative _⊔_
  ⊔-comm f g = fun-ext (λ x → L.⊔-comm (f x) (g x))
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong f g = fun-ext (λ x → L.⊔-cong₂ (cong (_$ x) f) (cong (_$ x) g))
  ⊔-assoc : Associative _⊔_
  ⊔-assoc f g h = fun-ext (λ x → L.⊔-assoc (f x) (g x) (h x))

  open Properties ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc
  
  lemma-wf : (f : ℂ) → (x : A) → Acc L._⊐_ (f x) -> Acc _⊐_ f
  lemma-wf f x (acc rs) = acc l
   where l : WfRec _⊐_ (Acc _⊐_) f
         l y x₁ with y x L.⊐? f x
         l y x₁ | yes p = lemma-wf y x (rs (y x) p)
         l y x₁ | no ¬p with all? (λ x → f x L.≟ y x) (Listable.all ls)
         l y x₁ | no ¬p | yes q = contradiction q (λ x₂ → ¬p ((cong (_$ x) (proj₁ x₁)) , (λ x₃ → {!!})))
         l y x₁ | no ¬p | no ¬q = {!!}
           -- ⊥-elim (¬p (cong (_$ x) (proj₁ x₁)  , {!proj₂ x₁!}))

 {-
  lemma-wf' : (f : ℂ) → ((x : A) → Acc L._⊐_ (f x)) -> (x : A) → Acc _⊐_ f
  lemma-wf' f x a with x a
  lemma-wf' f x a | acc rs = acc l         
   where l : WfRec _⊐_ (Acc _⊐_) f
         l y x₁ with y a L.⊐? f a
         l y x₁ | yes p = lemma-wf' y (λ x₂ → rs (y x₂) ({!!} , {!!})) {!!}
         l y x₁ | no ¬p = ⊥-elim (¬p (cong (_$ a) (proj₁ x₁)  , {!proj₂ x₁!})) -}

  {- ipv functie van A → Acc ;  een map van List.All → Acc    (Die kunnen we wel reducen?) -}


  lemma-wf'' : (f : ℂ) → ((x : A) → Acc L._⊐_ (f x)) -> Acc _⊐_ f
  lemma-wf'' f x = {!!}

 
  lemma-wf''' : (f : ℂ) → All (λ x → Acc L._⊐_ (f x)) (Listable.all ls) -> Acc _⊐_ f
  lemma-wf''' f xs = acc l
   where l : WfRec _⊐_ (Acc _⊐_) f
         l g (f⊑g , f≠g) with all? (λ x → f x L.≟ g x) (Listable.all ls)
         l g (f⊑g , f≠g) | yes p = contradiction (fun-ext (λ x → lookup p (Listable.complete ls x))) f≠g
         l g (f⊑g , f≠g) | no ¬p = {!!} --lemma-wf''' g (tabulate (λ x₁ → {!!})) --  → ∃ x :  f x ⊐ g x  -}


  ggg : {f g : ℂ} → {x : A} → Acc L._⊐_ (f x) → g x L.⊐ f x → Acc L._⊐_ (g x)
  ggg {f} {g} {x} (acc rs) x₂ = acc (λ y x → rs y (L.⊐-trans x x₂))

  open import Data.List.Any
  open import Data.Sum
  open Membership-≡
  
  newp : (xs : List A) → (_ : xs ≡ Listable.all ls) → (f : ℂ) → All (λ x → Acc L._⊐_ (f x)) xs -> Acc _⊐_ f
  newp [] refl f [] = acc (λ{ g (f⊑g , f≠g) → ⊥-elim (f≠g (fun-ext (λ{ x → ⊥-elim (case Listable.complete ls x of (λ{ ()}))})))})
  newp (x ∷ xs) refl f (px ∷ x₂) = acc (λ{ g (f⊑g , f≠g) → {!!}})

 
  -- g⊐f → x → g x ⊐ f x 

  mutual 
    lemma-wf'''' : (f : ℂ) → All (λ x → Acc L._⊐_ (f x)) (Listable.all ls) -> Acc _⊐_ f
    lemma-wf'''' f xs = acc (λ g x → {!∀-elim!} ) -- lemma-wf'''' g (helper₁ x xs) )
    -- P f     ∧     All (λ x → Q x) (Listable.all ..) ↔ Σ[ P ∈ Prop ] ((a : A) → P a)    ( a : A ) → P a                    ⇒   All (λ x → Q x) (Listable.all ..)
                                                                                 --          All (λ x → Q x) (Listable.all ..) ⇒ (a : A) → P a

    testt : {g : ℂ} → ((x : A) → Acc L._⊐_ (g x)) → Acc _⊐_ g
    testt x = {!fun-ext!}
 
   -- rewrite of helper₁ but without All
    helper₂ : {f g : ℂ} → (g⊐f : g ⊐ f) → ((x : A) → Acc L._⊐_ (f x)) → (x : A) → Acc L._⊐_ (g x)
    helper₂ {f} {g} g⊐f f-acc x = ∀-elim (λ y → Acc L._⊐_ (g y)) (Listable.all ls) (helper₁ g⊐f (tabulate (λ {y} y∈all → f-acc y))) x (Listable.complete ls x)

    helper₁ : {f g : ℂ} {xs : List A} → (g⊐f : g ⊐ f) → All (λ x → Acc L._⊐_ (f x)) xs → All (λ x → Acc L._⊐_ (g x)) xs
    helper₁ g⊐f [] = []
    helper₁ {f} {g} {x ∷ xs} g⊐f (px ∷ x₁) with g x L.⊒? f x
    helper₁ {f} {g} {x ∷ xs} g⊐f (acc rs ∷ x₁) | yes p = acc (λ y x₂ → rs y (L.⊑-trans p (proj₁ x₂) , (λ x₃ → proj₂ x₂ (L.⊑-antisym (proj₁ x₂) (subst (λ x₄ → x₄ L.⊔ g x ≡ g x) x₃ p))))) ∷ helper₁ g⊐f x₁
    helper₁ {f} {g} {x ∷ xs} g⊐f (acc rs ∷ x₁) | no ¬p = ⊥-elim (¬p (cong (_$ x) (proj₁ g⊐f)))

   {-
  lemma-wf : (x : ℂ) → Acc L._⊐_ (to x) → Acc _⊐_ x
  lemma-wf x (acc rs) = acc l
    where l : WfRec _⊐_ (Acc _⊐_) x
          l y x₁ with (to y) L.⊐? (to x)
          l y _ | yes p = lemma-wf y (rs (to y) p)
          l y (a , b) | no ¬p = ⊥-elim (¬p (trans (sym (right-inverse-of _)) (cong to a) , (λ x₁ → b (trans (trans (sym (left-inverse-of x)) (cong from x₁)) (left-inverse-of y)))))  
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = lemma-wf x (L.⊐-isWellFounded (to x))
 -}
   
  {-
  We lopen elk element af,
  we weten dat g ⊐ f.  (Dus er moet een element zijn zodat ..)
  we zijn bij x ∷ xs;
    stel dit element is: g x ⊐ f x ;   (kunnen we dan reducen?)
    stel dit element is: g x ≡ f x ;   (dan onthouden we dit en gaan we verder; als de lijst eenmaal leeg is; dan hebben we een contradictie)
  


  -}
  {-

 ∀ x    Acc L.⊐ (f x)   →   g x L.⊐ f x →  Acc (L.⊐) (g x)





 We know A is finite;
 We have a function f : A → B.
 We assume for every a ∈ A there is a proof such that everything bigger than (f a) is accessible.

 Suppose g ⊐ f.
   this means
     Σ a ∈ A : g a ⊐ f a   (however; which one)
   and ∀ a′ ∈ A : a′ ≠ a → g a ⊒ f a
   in words : All possible results of f are at least as big as the corresponding (pointwise) results for g and there is at least one element that is strictly bigger.

   Therefore, we can reduce the accessibility proof of (f a).

-}

  {-
  an easy way to prove accessibility is to show that all lower parts are accessible by pattern matching (thus breaking down the structure).
  But, we are unable to pattern match on a function and thus we somehow need to generate all the results.

  To generate the results, we need to start at the largest value, because for this value it is easy to show that everything greater is accessible, because there is nothing greater.
  Then we consider the functions f such that for any x,  f x ≤ ⊤ x

  the least function is the function that is 
  -}


  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded f = acc (λ{ g (a , b) → {!g!}}) -- lemma-wf''' f (tabulate (λ {a} x → L.⊐-isWellFounded (f a))) -- BoundedSemiLattice.⊐-isWellFounded (A -[ ? ]→ L)
   where open import LatticeTheory.TotalFunctionSpace hiding (fun-ext)
  --acc (λ{ y x → lemma-wf y {!!} {!!}}) --lemma-wf f (proj₁ (Listable.non-empty ls)) (L.⊐-isWellFounded (f (proj₁ (Listable.non-empty ls))))
                                                                   {- hier moeten we een a : A uit onze hoed toveren
                                                                       soort van ∀ introduction oid?

                                                                       Het geldt voor alle (a : A);
                                                                       we weten dat A listable is.
                                                                       Dat betekent dat of:
                                                                         A is empty
                                                                         A heeft aftelbaar veel elementen. en minstens een.

                                                                       
                                                                       een functie f is groter dan g als (voor alle (a : A) :  f a ⊑ g a )
                                                                       f ⊔ g = λ a → f a ⊔ g a
                                                                       f ⊑ g = λ a → f a ⊑ g a
                                                                       f ≡ g = λ a → f a ≡ g a
                                                                       
                                                                       f ≟ g = λ a → f a ≟ g a


 Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
 Decidable _∼_ = ∀ x y → Dec (x ∼ y)

 Iets is beslisbaar desda voor alle x en y geldt dat we ja of nee kunnen zeggen.

 Iets is beslisbaar desda voor alle (x → x′  en y → y′) geldt dat we voor alle

 Dec ((a : A) → f a ∼ g a)
 Dec ((a : A) → (b : B) → f a b ∼ g a b)


 als je kunt laten zien dat het voor alle A geldt, en A is eindig; dan kunnen we aannemen dat het (globaal) geldt?
 WellFounded =  ∀ x → Acc _<_ x

 data Acc {a ℓ} {A : Set a} (_<_ : Rel A ℓ) (x : A) : Set (a ⊔ ℓ) where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

                                                                    -}
{-
data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
-}

-- (Quantified relation)
 {-
  q : ∀{α β f} → {A : Set α} → {B : Set β} → {f : A → B} → Dec ((a : A) → {!!})
  q = {!!} -}
{-

  lemma-wf : (x : ℂ) → Acc L._⊐_ (to x) → Acc _⊐_ x
  lemma-wf x (acc rs) = acc l
    where l : WfRec _⊐_ (Acc _⊐_) x
          l y x₁ with (to y) L.⊐? (to x)
          l y _ | yes p = lemma-wf y (rs (to y) p)
          l y (a , b) | no ¬p = ⊥-elim (¬p (trans (sym (right-inverse-of _)) (cong to a) , (λ x₁ → b (trans (trans (sym (left-inverse-of x)) (cong from x₁)) (left-inverse-of y)))))  
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = lemma-wf x (L.⊐-isWellFounded (to x))
  -}
--  f is groter dan een g als voor alle x geldt dat f x ⊒ g x

