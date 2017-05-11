open import Data.Vec
open import Data.Bool
open import Data.Product
open import While.Language 
open import While.Analysis.AvailableExpressions
open import Data.Fin
open import Data.List
module While.Examples where

module LV where
  open import While.Examples.LiveVariables public
  
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
  open import While.Examples.AvailableExpressions public
  {- expected bogus₂    [AExpr⋆ = a + b, a * b , a + b, a + 1, a + b]
  AExpr○      AExpr●
   ∅         {a+b}
   {a+b}      {a+b,a*b}
   {a+b}      {a+b}
   {a+b}      ∅
   ∅         {a+b}
   -}
module CP where
  open import While.Examples.ConstantPropagation public
