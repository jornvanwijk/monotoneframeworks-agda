open import Data.Fin
open import Data.Product
open import While.Language 
import Data.Graph
open import Data.Integer
module While.Programs.Bogus-2 where

open Unlabeled

bogus₂ : Stmt
bogus₂ = "x" := var "a" plus var "b" seq
         "y" := var "a" mul var "b" seq
         while var "y" gt var "a" plus var "b" do
         (
           "a" := var "a" plus lit (+ 1) seq
           "x" := var "a" plus var "b"
         )
 
open Labeled
open Generated bogus₂ renaming (whileProgram to bogus₂-labeled) public
