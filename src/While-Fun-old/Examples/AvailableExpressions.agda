open import Data.Product
open import Data.Fin.Subset
open import Data.Vec
open import While.Analysis.AvailableExpressions as AE
open import Algorithms
open import Data.List
module While.Examples.AvailableExpressions where

open import While.Examples.Common available-expressions public
{-


open import While.Programs.Factorial
open import Data.Fin

fac-chaotic : Vec (Subset (length (AExpr⋆ 6 3 fac))) 6 × Vec (Subset (length (AExpr⋆ 6 3 fac))) 6
fac-chaotic = chaotic-result (available-expressions 6 3 fac)

fac-parallel : Vec (Subset (length (AExpr⋆ 6 3 fac))) 6 × Vec (Subset (length (AExpr⋆ 6 3 fac))) 6
fac-parallel = parallel-result (available-expressions 6 3 fac)

fac-mfp : Vec (Subset (length (AExpr⋆ 6 3 fac))) 6 × Vec (Subset (length (AExpr⋆ 6 3 fac))) 6
fac-mfp = mfp-result (available-expressions 6 3 fac)



open import While.Programs.Bogus-2
open import While.Language

open import MonotoneFramework
mf : MonotoneFramework _ _
mf = (available-expressions 5 4 bogus₂)

bogus₂-chaotic : Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5 × Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5
bogus₂-chaotic = chaotic-result (available-expressions 5 4 bogus₂)

bogus₂-parallel : Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5 × Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5
bogus₂-parallel = parallel-result (available-expressions 5 4 bogus₂)

bogus₂-parallel-tfs : Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5 × Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5
bogus₂-parallel-tfs = let (a , b) = solveFr (available-expressions 5 4 bogus₂) in (tabulate a , tabulate b) 

bogus₂-mfp : Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5 × Vec (Subset (length (AExpr⋆ 5 4 bogus₂))) 5
bogus₂-mfp = mfp-result (available-expressions 5 4 bogus₂)
-}
{-
AExpr⋆ = var a plus var b ∷ var a mul var b ∷ var a plus var b ∷ var a plus lit 1 ∷ var a plus var b ∷ []

expected:
  AExpr○      AExpr●
   ∅         {a+b}
   {a+b}      {a+b,a*b}
   {a+b}      {a+b}
   {a+b}      ∅
   ∅         {a+b}

encoded as:
(outside ∷ outside ∷ outside ∷ outside ∷ outside ∷ []) ∷
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(outside ∷ outside ∷ outside ∷ outside ∷ outside ∷ []) ∷ []
,
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(inside ∷ inside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷
(outside ∷ outside ∷ outside ∷ outside ∷ outside ∷ []) ∷
(inside ∷ outside ∷ inside ∷ outside ∷ inside ∷ []) ∷ []




open import While.Programs.Bogus-1

bogus-chaotic : Vec (Subset 3) 7 × Vec (Subset 3) 7
bogus-chaotic = chaotic-result (available-expressions 7 3 bogus)

parallel-chaotic : Vec (Subset 3) 7 × Vec (Subset 3) 7
parallel-chaotic = parallel-result (available-expressions 7 3 bogus)

bogus-mfp : Vec (Subset 3) 7 × Vec (Subset 3) 7
bogus-mfp = mfp-result (available-expressions 7 3 bogus)
  
bogus-parallel-tfs : Vec (Subset 3) 7 × Vec (Subset 3) 7
bogus-parallel-tfs = let (a , b) = solveFr (available-expressions 7 3 bogus) in (tabulate a , tabulate b) 
-}
