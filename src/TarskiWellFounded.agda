open import LatticeTheory
open import Induction.WellFounded
open import Monotonicity
open import Relation.Nullary.Negation
open import Algebra.Properties.Lattice
open import Relation.Binary
import Level
open import Data.Product renaming (_×_ to _⋀_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Function
open import Relation.Binary.PropositionalEquality

module TarskiWellFounded {a}  (completeLattice : BoundedSemiLattice a) (open BoundedSemiLattice completeLattice) (f : ℂ -> ℂ) (isMonotone : Monotone _⊑_ f) where

  
  open import Data.FixedPoint.FixedPoint completeLattice f public
  open FixedPoint


  
  module _ (efp : FixedPoint) where
    -- Suppose that efp (e) is a fixed point with p as proof.
    private
      x : ℂ
      x = element efp

    private 
      x⊑fx : x ≡ f x
      x⊑fx = isFixedPoint efp

    -- then we can show that ⊥ is lower or equal to e
    lfp-base : ⊥ ⊑ x
    lfp-base = ⊥-isMinimal x

    -- and inductively, if some c is lower or equal to e
    -- c ⊑ e ⇒ f c ⊑ f e ⊑ e 
    lfp-step : {y : ℂ} -> y ⊑ x -> f y ⊑ x
    lfp-step y⊑x = ⊑-trans (isMonotone y⊑x) (fixed⇒reductive x⊑fx)


  -- To find our least fixed point, we need to start at an extensive point.
  -- ⊥ is such a point.
  fp-base : IsExtensivePoint ⊥
  fp-base = ⊥-isMinimal (f ⊥)

  -- if we have an extensive point c , then due to monotonicity f c is also extensive
  fp-step : ∀{x} -> IsExtensivePoint x → IsExtensivePoint (f x)
  fp-step = isMonotone

  -- given an extensive point, a proof of the ascending chain condition (or _⊑_ being conversely well founded)
  -- we find a fixed point, and construct a proof that it is the least one.
  l₀-rec : {x : ℂ} -> x ⊑ f x -> ((e : FixedPoint) -> x ⊑ element e ) -> Acc _⊐_ x -> LeastFixedPoint
  l₀-rec {x} x⊑fx x⊑l₀ (acc g) with x ≟ (f x)
  l₀-rec {x} x⊑fx q (acc g) | yes r = lfp x (r , q)
  l₀-rec {x} x⊑fx q (acc g) | no ¬r = l₀-rec (fp-step x⊑fx) (λ e → lfp-step e (q e)) (g (f x) (x⊑fx , ¬r))

  {- note that we require ⊒ to be conversely well founded to let agda know this terminates
  l₀-rec' : {c : ℂ} -> c ⊑ f c -> ((e : FixedPoint) -> c ⊑ element e ) -> LeastFixedPoint
  l₀-rec' {c} x x₁ with c ≟ f c
  l₀-rec' {c} x x₁ | yes p = lfp c (p , x₁)
  l₀-rec' {c} x x₁ | no ¬p = l₀-rec' (fp-step x) (λ e → lfp-step e (x₁ e))
  -}

  -- application of l₀-rec with initial values
  l₀-lfp : LeastFixedPoint
  l₀-lfp = l₀-rec fp-base lfp-base (⊐-isWellFounded ⊥)

  -- the least fixed point
  l₀ : ℂ
  l₀ = LeastFixedPoint.element l₀-lfp

  -- synonym for l₀
  solveLeastFixedPoint : ℂ
  solveLeastFixedPoint = l₀
