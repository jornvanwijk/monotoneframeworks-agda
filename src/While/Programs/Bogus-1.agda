open import Data.Fin
open import Data.Product
open import While.Language
import Data.Graph
open import Data.Integer hiding (suc)
module While.Programs.Bogus-1 where
open Unlabeled

bogus : Stmt
bogus = "x" := lit (+ 2) seq
        "y" := lit (+ 4) seq
        "x" := lit (+ 1) seq
        (if var "y" gt var "x"
        then "z" := var "y"
        else "z" := var "y" mul var "y") seq
        "x" := var "z" 


open Labeled
open Generated bogus renaming (whileProgram to bogus-labeled) public
