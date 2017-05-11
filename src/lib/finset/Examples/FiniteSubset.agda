

module Examples.FiniteSubset where

open import Relation.Binary.PropositionalEquality hiding (inspect)

open import Data.Product
open import Data.List hiding (product)
open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Data.Unit

open import Utilities.ListProperties

open import FiniteSubset
open import Finiteness

open import Examples.Pauli


-- MyNats1 is a newly defined finite subset of natural numbers
MyNats1 : FiniteSubSet ℕ Data.Nat._≟_ false
MyNats1 = fs-nojunk (1 ∷ 3 ∷ [])

-- we could generate all the elements of MyNats1
elements : List (Element MyNats1)
elements = elementsOf MyNats1

-- Elements of MyNats1 are the pairs of natural numbers together
-- with the squashed proof of their inclusion in the underlying list
-- of MyNats1
prf : elements ≡ (1 , tt) ∷ (3 , tt) ∷ []
prf = refl


-- MyNats1Elements is complete
elementsComplete : ∀ p → p ∈ elements
elementsComplete = elementsOfComplete MyNats1


-- we could define another finite subset of natural numbers
MyNats2 : FiniteSubSet ℕ Data.Nat._≟_ false
MyNats2 = fs-nojunk (1 ∷ 6 ∷ [])


-- now we could use the combinators of FiniteSubset
-- to get new finite subsets
p : MyNats1 ∩ MyNats2 ≡ fs-nojunk (1 ∷ [])
p = refl


