open import Data.Fin
open import Data.Product
import While.Language as While
import Data.Graph
open import Data.Integer hiding (suc)
module While.Programs.Bogus-1 where
  
x : Fin 3
x = zero
y : Fin 3
y = suc zero
z : Fin 3
z = suc (suc zero)

open While 7 3
open Data.Graph 7
bogus : Stmt
bogus = (x := lit (+ 2)) (# 0) seq
        (y := lit (+ 4)) (# 1) seq
        (x := lit (+ 1)) (# 2) seq
        (if var y gt var x , # 3 
        then (z := var y) (# 4)
        else (z := var y mul var y) (# 5)) seq
        (x := var z) (# 6)
 
