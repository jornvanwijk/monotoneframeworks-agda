open import Data.Product
open import Data.Fin.Subset
open import Data.Vec
open import Algorithms
open import MonotoneFramework
open import Data.Nat
open import LatticeTheory.Core
open import While-Fun.Language
import Level
open import Data.String
open Labeled
module While-Fun.Examples.Common (createMonotoneFramework : (program : WhileProgram) → (open WhileProgram program) →  MonotoneFramework Level.zero)
  (showAnalysis : (program : WhileProgram) → (open MonotoneFramework.MonotoneFramework (createMonotoneFramework program)) → (open BoundedSemiLattice L) → (ℂ → String)) where


showExample : ∀{a} → (mf : MonotoneFramework a ) → (open MonotoneFramework.MonotoneFramework mf) → (open BoundedSemiLattice L) → (ℂ → String) → Vec ℂ n × Vec ℂ n → String
showExample MF f (ana○ , ana●) = "Analysis○: \n" Data.String.++ MonotoneFramework.showℂ MF f ana○ Data.String.++ "\nAnalysis●:\n" Data.String.++ MonotoneFramework.showℂ MF f ana●

module _ where
  open import While-Fun.Programs.Bogus-1
  open WhileProgram bogus-labelled hiding (n)
  MF-bogus : MonotoneFramework Level.zero
  MF-bogus = createMonotoneFramework bogus-labelled

  open MonotoneFramework.MonotoneFramework MF-bogus
  open BoundedSemiLattice L

  bogus-chaotic : Vec ℂ n × Vec ℂ n
  bogus-chaotic = chaotic-result MF-bogus

  bogus-parallel : Vec ℂ n × Vec ℂ n
  bogus-parallel = parallel-result MF-bogus

  bogus-mfp : Vec ℂ n × Vec ℂ n
  bogus-mfp = mfp-result MF-bogus
  
  bogus-parallel-tfs : Vec ℂ n × Vec ℂ n
  bogus-parallel-tfs = parallel-tfs-result MF-bogus


  showBogus : String
  showBogus = "bogus-parallel\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labelled) bogus-parallel
    Data.String.++ "\nbogus-parallel-tfs\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labelled) bogus-parallel-tfs
    Data.String.++ "\nbogus-chaotic\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labelled) bogus-chaotic
    Data.String.++ "\nbogus-mfp\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labelled) bogus-mfp

showAll : String
showAll = showBogus  Data.String.++ "\n\n"
