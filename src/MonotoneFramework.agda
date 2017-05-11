import Level
open import Agda.Builtin.Equality
open import Algebra.FunctionProperties
open import Category.Monad
open import Category.Monad.Partiality renaming (_⊥ to _ℙ⊥)
open import Category.Monad.Partiality.All
open import Coinduction
open import Data.Bool
open import Data.Fin
open import Data.List as 𝕃
open import Data.List.Any
open import Data.Maybe
open import Data.Nat hiding (_⊔_ ; _⊓_)
open import Data.Product
open import Data.Vec as 𝕍 hiding (head) 
open import Data.Graph
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import LatticeTheory
-- open import LatticeTheory as ℂ𝕃
open import Monotonicity
open import Data.Fin.Properties as FinP
open import Data.String
open import ExtendedFramework
open import Util.Subset
module MonotoneFramework where

  record MonotoneFramework a : Set (Level.suc a) where
    field
      n : ℕ
      L : BoundedSemiLattice a -- Lattice instance
    open BoundedSemiLattice L -- public
    Label : Set
    Label = Fin n
    field
      𝓕 : Label -> ℂ -> ℂ  -- Set of transfer functions indexed by label   --todo monotonicity constraint
      F : Graph n          -- Control flow graph
      E : List Label    -- Extremal labels                               
      ι : ℂ                -- Extremal value
      𝓕-isMonotone : (ℓ : Fin n) → Monotone _⊑_ (𝓕 ℓ)

    𝑓 : Label → Vec ℂ n → ℂ
    𝑓 ℓ x = 𝓕 ℓ (lookup ℓ x)


    ιE : Label → ℂ
    ιE ℓ′ = if ⌊ Data.List.Any.any (FinP._≟ ℓ′) E ⌋
          then ι
          else ⊥
    
    initial : Vec ℂ n
    initial = tabulate ιE



    open ProductEncoding
    open Containment {Level.zero} {n * n} {Fin n × Fin n} (ℕ×ℕ↔ℕ n) 
    asExtendedFramework : ExtendedFramework a
    ExtendedFramework.n asExtendedFramework = n
    ExtendedFramework.L asExtendedFramework = L
    ExtendedFramework.𝓕 asExtendedFramework = 𝓕
    ExtendedFramework.next asExtendedFramework = λ x x₁ → list-to-set F 
    ExtendedFramework.E asExtendedFramework = E
    ExtendedFramework.ι asExtendedFramework = ι
    ExtendedFramework.𝓕-isMonotone asExtendedFramework = 𝓕-isMonotone
    ExtendedFramework.next-isMonotone asExtendedFramework = λ ℓ x₁ → BoundedSemiLattice.⊔-idem (𝓟ᴸ-by-inclusion (n * n)) _

    showℂ : (ℂ → String) → Vec ℂ n → String
    showℂ f x = 𝕍.foldr (λ x₁ → String) (λ x₁ x₂ → f x₁ Data.String.++ "\n" Data.String.++ x₂) "" x -- unlines (𝕍.toList (𝕍.map f x))
    {-
    = unlines (Data.Vec.toList (Data.Vec.map (λ f → Data.String.fromList (Data.List.concat (intersperse (Data.String.toList ", ") (Data.Vec.toList (Data.Vec.map (λ v → Data.String.toList (showℤ⊤⊥ (f v))) (allFin _)))))) x)) --Data.Vec.map (λ f → Data.Vec.map f (allFin 3)) x
-}

    --modality : ↕
    --direction : ↔
