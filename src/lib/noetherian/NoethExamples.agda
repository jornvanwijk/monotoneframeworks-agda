

module NoethExamples where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Utilities
open import Noetherian


BoolNoeth : NoethAcc Bool
BoolNoeth  = ask (λ  { true → ask (λ { true → stop (duphere (here refl)) 
                                      ; false → ask (λ { true → stop dup1 
                                                        ; false → stop dup2 }) 
                                        }) 
                      ; false → ask (λ { true → ask (λ { true → stop dup2 
                                                         ; false → stop dup1 }) 
                                        ; false → stop (duphere (here refl)) })  })

   where
    dup1 : {x y : Bool} → Dup (x ∷ y ∷ x ∷ [])
    dup1 {x} {y} = duphere (there (here refl)) 

    dup2 : {x y : Bool} → Dup (x ∷ x ∷ y ∷ [])
    dup2 {x} {y} = duphere (here refl)
