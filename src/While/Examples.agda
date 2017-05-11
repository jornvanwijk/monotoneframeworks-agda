open import Data.Vec
open import Data.Bool
open import Data.Product
open import While.Analysis.AvailableExpressions
open import Data.Fin
open import Data.List
open import Data.String
open import IO
open import Function
open import MonotoneFramework
open import LatticeTheory
module While.Examples where




open import While.Programs.Factorial
module EXA where
  open import While.Analysis.LiveVariables fac-labeled
  open import While.Language
  open Labeled.WhileProgram fac-labeled hiding (n)

  open MonotoneFramework.MonotoneFramework live-variables
  open BoundedSemiLattice L
  open import Algorithms
  
  fac-mfp : Vec ℂ n × Vec ℂ n
  fac-mfp = mfp-result live-variables


module LV where
  open import While.Analysis.LiveVariables public
  open import While.Examples.Common live-variables showLV public
  
  {- expected solution LiveVariables bogus:
  solution●   solution○
    ∅         ∅
    ∅         {y}
    {y}        {x,y}
    {x,y}      {y}
    {y}        {z}
    {y}        {z}
    {z}        ∅
  -}
  
module AE where
  open import While.Analysis.AvailableExpressions public
  open import While.Examples.Common available-expressions showAE public
  {- expected bogus₂    [AExpr⋆ = a + b, a * b , a + b, a + 1, a + b]
  AExpr○      AExpr●
   ∅         {a+b}
   {a+b}      {a+b,a*b}
   {a+b}      {a+b}
   {a+b}      ∅
   ∅         {a+b}
   -}
module CP where
  open import While.Analysis.ConstantPropagation public
  open import While.Examples.Common constant-propagation showCP public

result : String
result = LV.showAll Data.String.++ AE.showAll Data.String.++ CP.showAll

main =  run ∘ putStrLn $ result

