open import Data.Product
open import Data.Fin.Subset
open import Data.Vec
open import While.Analysis.LiveVariables
open import Algorithms
open import MonotoneFramework
open import Data.Nat
open import LatticeTheory.Core
open import While.Language
import Level
open import Data.String
open Labeled
module While.Examples.Common (createMonotoneFramework : (program : WhileProgram) → (open WhileProgram program) → MonotoneFramework Level.zero)
  (showAnalysis : (program : WhileProgram) → (open MonotoneFramework.MonotoneFramework (createMonotoneFramework program)) → (open BoundedSemiLattice L) → (ℂ → String)) where


showExample : ∀{a} → (mf : MonotoneFramework a) → (open MonotoneFramework.MonotoneFramework mf) → (open BoundedSemiLattice L) → (ℂ → String) → Vec ℂ n × Vec ℂ n → String
showExample MF f (ana○ , ana●) = "Analysis○: \n" Data.String.++ MonotoneFramework.showℂ MF f ana○ Data.String.++ "\nAnalysis●:\n" Data.String.++ MonotoneFramework.showℂ MF f ana●


module _ where
  open import While.Programs.Factorial
  open WhileProgram fac-labeled hiding (n)
  MF-fac : MonotoneFramework Level.zero
  MF-fac = createMonotoneFramework fac-labeled

  open MonotoneFramework.MonotoneFramework MF-fac
  open BoundedSemiLattice L

  fac-chaotic : Vec ℂ n × Vec ℂ n
  fac-chaotic = chaotic-result MF-fac

  fac-parallel : Vec ℂ n × Vec ℂ n
  fac-parallel = parallel-result MF-fac

  fac-mfp : Vec ℂ n × Vec ℂ n
  fac-mfp = mfp-result MF-fac

  fac-parallel-tfs : Vec ℂ n × Vec ℂ n
  fac-parallel-tfs = parallel-tfs-result MF-fac

  showFac : String
  showFac = "fac-parallel\n" Data.String.++ showExample MF-fac (showAnalysis fac-labeled) fac-parallel
    Data.String.++ "\nfac-parallel-tfs\n" Data.String.++ showExample MF-fac (showAnalysis fac-labeled) fac-parallel-tfs
    Data.String.++ "\nfac-chaotic\n" Data.String.++ showExample MF-fac (showAnalysis fac-labeled) fac-chaotic
    Data.String.++ "\nfac-mfp\n" Data.String.++ showExample MF-fac (showAnalysis fac-labeled) fac-mfp

module _ where
  open import While.Programs.Bogus-1
  open WhileProgram bogus-labeled hiding (n)
  MF-bogus : MonotoneFramework Level.zero
  MF-bogus = createMonotoneFramework bogus-labeled

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
  showBogus = "bogus-parallel\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labeled) bogus-parallel
    Data.String.++ "\nbogus-parallel-tfs\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labeled) bogus-parallel-tfs
    Data.String.++ "\nbogus-chaotic\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labeled) bogus-chaotic
    Data.String.++ "\nbogus-mfp\n" Data.String.++ showExample MF-bogus (showAnalysis bogus-labeled) bogus-mfp

module _ where
  open import While.Programs.Bogus-2
  open WhileProgram bogus₂-labeled hiding (n)
  MF-bogus₂ : MonotoneFramework Level.zero
  MF-bogus₂ = createMonotoneFramework bogus₂-labeled
    
  open MonotoneFramework.MonotoneFramework MF-bogus₂
  open BoundedSemiLattice L

  bogus₂-chaotic : Vec ℂ n × Vec ℂ n
  bogus₂-chaotic = chaotic-result MF-bogus₂

  bogus₂-parallel : Vec ℂ n × Vec ℂ n
  bogus₂-parallel = parallel-result MF-bogus₂

  bogus₂-mfp : Vec ℂ n × Vec ℂ n
  bogus₂-mfp = mfp-result MF-bogus₂

  bogus₂-parallel-tfs : Vec ℂ n × Vec ℂ n
  bogus₂-parallel-tfs = parallel-tfs-result MF-bogus₂


  showBogus₂ : String
  showBogus₂ = "bogus₂-parallel\n" Data.String.++ showExample MF-bogus₂ (showAnalysis bogus₂-labeled) bogus₂-parallel
    Data.String.++ "\nbogus₂-parallel-tfs\n" Data.String.++ showExample MF-bogus₂ (showAnalysis bogus₂-labeled) bogus₂-parallel-tfs
    Data.String.++ "\nbogus₂-chaotic\n" Data.String.++ showExample MF-bogus₂ (showAnalysis bogus₂-labeled) bogus₂-chaotic
    Data.String.++ "\nbogus₂-mfp\n" Data.String.++ showExample MF-bogus₂ (showAnalysis bogus₂-labeled) bogus₂-mfp

module _ where
  open import While.Programs.Bogus-3
  open WhileProgram bogus₃-labeled hiding (n)
  MF-bogus₃ : MonotoneFramework Level.zero
  MF-bogus₃ = createMonotoneFramework bogus₃-labeled

  open MonotoneFramework.MonotoneFramework MF-bogus₃
  open BoundedSemiLattice L

  bogus₃-chaotic : Vec ℂ n × Vec ℂ n
  bogus₃-chaotic = chaotic-result MF-bogus₃

  bogus₃-parallel : Vec ℂ n × Vec ℂ n
  bogus₃-parallel = parallel-result MF-bogus₃

  bogus₃-mfp : Vec ℂ n × Vec ℂ n
  bogus₃-mfp = mfp-result MF-bogus₃

  bogus₃-parallel-tfs : Vec ℂ n × Vec ℂ n
  bogus₃-parallel-tfs = parallel-tfs-result MF-bogus₃


  showBogus₃ : String
  showBogus₃ = "bogus₃-parallel\n" Data.String.++ showExample MF-bogus₃ (showAnalysis bogus₃-labeled) bogus₃-parallel
    Data.String.++ "\nbogus₃-parallel-tfs\n" Data.String.++ showExample MF-bogus₃ (showAnalysis bogus₃-labeled) bogus₃-parallel-tfs
    Data.String.++ "\nbogus₃-chaotic\n" Data.String.++ showExample MF-bogus₃ (showAnalysis bogus₃-labeled) bogus₃-chaotic
    Data.String.++ "\nbogus₃-mfp\n" Data.String.++ showExample MF-bogus₃ (showAnalysis bogus₃-labeled) bogus₃-mfp

showAll : String
showAll = showFac Data.String.++ "\n\n" Data.String.++ showBogus  Data.String.++ "\n\n" Data.String.++ showBogus₂  Data.String.++ "\n\n" Data.String.++ showBogus₃
