

module Examples.PredicateMatching where


open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary
open import Relation.Nullary

open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_⊔_)


open import Utilities.ListProperties 
open import Utilities.Logic

open import Finiteness
open import FiniteSubset
open import Tabulation
open import PredicateMatching


-- We could define a subset of first 10 natural numbers
MyNats : FiniteSubSet ℕ _≟_ false
MyNats = fs-nojunk (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [])

-- Defining functions by explicitly providing the table would not be very 
-- efficient (binary functions require 100 entries). So, we going to use
-- the concept of predicate matching. 

-- First, we define predicates on natural numbers
mutual
 even : ℕ → Bool
 even zero = true
 even (suc n) = odd n

 odd : ℕ → Bool
 odd zero = false
 odd (suc n) = even n 

-- Next, we want to write a function which double the even numbers and
-- triples the odd ones. We do that by providing the list of
-- predicate--function pairs. Typecheckers controls that all elements
-- of MyNats are reached and no pair of predicate--function is unreacheable
odds+3ev+2 : Element MyNats → ℕ
odds+3ev+2 = PMtofun (makePM MyNats equations refl refl)
  where
   equations = 
     (fromPure MyNats odd  , (λ { (x , _ ) → 3 * x })) ∷
     (fromPure MyNats even , (λ { (x , _ ) → 2 * x  })) ∷ []



-- The next example illustrates what happens if one of the predicates
-- is unreacheable. Then you are asked to provide the proof of
-- fromPure MyNats even ∷ [] ≡ []. The goal provides the clue of what
-- equation is unreacheable.
{-
odds+3ev+2Bad1 : Element MyNats → ℕ
odds+3ev+2Bad1 = PMtofun (makePM MyNats equations {!!} refl)
  where
   equations = 
     (fromPure MyNats (λ _ → true)  , (λ { (x , _ ) → 3 * x })) ∷
     (fromPure MyNats even , (λ { (x , _ ) → 2 * x  })) ∷ []
-}



-- In this example, we have incomplete predicate matching since we
-- forgot to include the case for odd numbers. The typechecker
-- supplies us with the goal to prove: 1 ∷ 3 ∷ 5 ∷ 7 ∷ 9 ∷ [] ≡
-- []. This again gives us a clues of what elements were not matched.
{-
odds+3ev+2Bad2 : Element MyNats → ℕ
odds+3ev+2Bad2 = PMtofun (makePM MyNats equations refl {!!})
  where
   equations = 
     (fromPure MyNats even , (λ { (x , _ ) → 2 * x  })) ∷ []
-}
