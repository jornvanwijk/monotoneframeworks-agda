open import Data.Fin
open import Data.Product
open import While.Language
import Data.Graph
open import Data.Integer hiding (suc)
module While.Programs.Bogus-3 where

open Unlabeled

bogus₃ : Stmt
bogus₃ = "y" := lit (+ 2) seq
         "z" := lit (+ 1) seq
         while var "x" gt lit (+ 0)
           do ("z" := var "z" mul var "y") seq
         "x" := var "x" min lit (+ 1)

open Labeled
open Generated bogus₃ renaming (whileProgram to bogus₃-labeled) public
