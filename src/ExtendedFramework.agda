open import LatticeTheory
import Level
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Fin.Properties as FinP
open import Data.List as 𝕃
open import Data.Vec
open import Data.Bool
open import Monotonicity
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.List.Any
open import Function.Inverse using (_↔_ ; Inverse)
open import Data.Product
open import Data.Fin.Dec
open import Data.Fin.Properties as FinP
open import Util.Subset
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Subset renaming (⊥ to ∅)
open import Relation.Nullary.Negation
import Relation.Binary.List.Pointwise as Pointwise
open import Induction.WellFounded
open import Data.Vec.Properties
open import Function

{- Agda version 2.5.2

1) BijectiveToFin   Util/BoundedList
  -- bijectie maken door middel van opsomming   (lookup  en index-of)
3) Architectuur
     instances  show
     ⊑ en abstract     (Tryout/Abstract)
       een oplossing:
         data lattice where
           abstract
             _⊔_ : A → A → A
           _⊔-def_ : A → A → A
           toDefinition : ∀{x y}  x ⊔ y ≡ x ⊔-def y

   Daarnaast dus eventueel een record voor een product maken met regels voor het product in die record
   die vervolgens ook een lattice is.
4) Dependent product(?)   (deze file)
     Toch beter om te kijken of we de CFG niet in de lattice stoppen
     maar daarbuiten
     en in de fix point op te nemen dat ook next een fix point behaalt.

5) Total Function space    (vector veranderen naar een functie)
-}

module ExtendedFramework where

  module ProductEncoding (n : ℕ) where

-- To encode (x,y) -> z:

  {-
  to′ : (ℕ × ℕ) → ℕ
  to′ (x , y) = ⌊ (x Data.Nat.+ y) * (x Data.Nat.+ y Data.Nat.+ 1) /2⌋ Data.Nat.+ y

  from′ : ℕ → (ℕ × ℕ)
  from′ = {!!}


-- z=((x+y)(x+y+1))/2+y
  
  to : Fin n × Fin n → Fin (n * n)
  to (ℓ , ℓ′) = let x = toℕ ℓ
                    y = toℕ ℓ′
               in {!⌊ (x Data.Nat.+ y) * (x Data.Nat.+ y Data.Nat.+ 1) /2⌋ Data.Nat.+ y!}
  -}
    postulate
      ℕ×ℕ↔ℕ : (Fin n × Fin n) ↔ Fin (n * n)
  {-
  Inverse.to ℕ×ℕ↔ℕ = →-to-⟶ {!to′!}
  Inverse.from ℕ×ℕ↔ℕ = {!!}
  Inverse.inverse-of ℕ×ℕ↔ℕ = {!!}
  -}


  record ExtendedFramework a : Set (Level.suc a) where
    field
      n : ℕ
      L : BoundedSemiLattice a -- Lattice instance
    open LatticeTheory.BoundedSemiLattice L -- public
    Label : Set
    Label = Fin n
    CFG : Set
    CFG = Subset (n * n)
    Fᴸ : BoundedSemiLattice _
    Fᴸ = 𝓟ᴸ-by-inclusion (n * n)
    field
      𝓕 : Label -> ℂ -> ℂ  -- Set of transfer functions indexed by label   --todo monotonicity constraint
      next : Label → ℂ → CFG -- function that given information provides new edges for the control flow graph.   -- wondering if we should add previous flow to the next function (next : Label → CFG → 𝕔 → CFG
      E : List Label    -- Extremal labels                               
      ι : ℂ                -- Extremal value
      𝓕-isMonotone : (ℓ : Fin n) → Monotone _⊑_ (𝓕 ℓ)
      next-isMonotone : (ℓ : Fin n) → Monotone₂ _⊑_ (BoundedSemiLattice._⊑_ Fᴸ) (next ℓ)
                                                  
    𝑓 : Label → Vec ℂ n → ℂ
    𝑓 ℓ x = 𝓕 ℓ (lookup ℓ x)
                        

    ιE : Label → ℂ
    ιE ℓ′ = if ⌊ Data.List.Any.any (FinP._≟ ℓ′) E ⌋
           then ι
           else ⊥

    initial : Vec ℂ n
    initial = tabulate ιE


    open import Data.List
    private 
      module F where
        open BoundedSemiLattice Fᴸ public
        open BoundedSemiLattice.Reasoning Fᴸ public
    initial-F : CFG
    initial-F = F.⨆ (Data.List.map (λ ℓ → next ℓ (lookup ℓ initial)) (Data.Vec.toList (allFin n)))
{-
open Definition
-}
