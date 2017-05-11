

module Examples.Tabulation where 

open import Relation.Binary.PropositionalEquality hiding (inspect)

open import Data.Product
open import Data.List hiding (product)

open import Finiteness
open import Function 

open import Tabulation 
  hiding (_↦_)

open import Examples.Pauli


-- Tabulation is convenient to use for small sets like Pauli
shiftPauli : Pauli → Pauli
shiftPauli = fromTbl $ createTbl 
   (X ↦ Y ∷ 
    Y ↦ Z ∷ 
    Z ↦ I ∷ 
    I ↦ X ∷ [])
   (listPauli , allPauli)
     where
       _↦_ =  _,_


-- On the other hand, the following is not going to typecheck, because
-- the list is not complete (case for I is missing)
{-
shiftPauliBad1 : Pauli → Pauli
shiftPauliBad1 = fromTbl $ createTbl 
   (X ↦ Y ∷ 
    Y ↦ Z ∷ 
    Z ↦ I ∷  [])
   (listPauli , allPauli) {{!!}}
     where
       _↦_ =  _,_
-}


-- The following is also not going to typecheck, because the list
-- is ambiguous (X is mapped to Y and to Z)
{-
shiftPauliBad2 : Pauli → Pauli
shiftPauliBad2 = fromTbl $ createTbl 
   (X ↦ Y ∷ 
    Y ↦ Z ∷ 
    Z ↦ I ∷
    X ↦ Z ∷  [])
   (listPauli , allPauli) {{!!}}
     where
       _↦_ =  _,_
-}
