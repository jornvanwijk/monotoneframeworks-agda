module Util.Function where

open import Function



const₂ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} -> A -> B -> C -> A
const₂ = const ∘ const

const₃ : ∀{a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} -> A -> B -> C → D -> A
const₃ = const ∘ const₂
