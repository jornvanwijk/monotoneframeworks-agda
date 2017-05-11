open import Data.Product
open import Data.Fin.Subset
open import Data.Vec
open import While.Analysis.LiveVariables
open import Algorithms
open import MonotoneFramework
open import While.Language
open import Data.Nat
open import LatticeTheory.Core
import Level
module While.Examples.Common (createMonotoneFramework : (n : ℕ) → (m : ℕ) → Stmt n m → MonotoneFramework Level.zero n) where

module _ where
  open import While.Programs.Factorial
  private 
    n : ℕ
    n = 6
    m : ℕ
    m = 3
    MF : MonotoneFramework Level.zero n
    MF = createMonotoneFramework n m fac

  open MonotoneFramework.MonotoneFramework MF
  open BoundedSemiLattice L

  fac-chaotic : Vec ℂ n × Vec ℂ n
  fac-chaotic = chaotic-result MF

  fac-parallel : Vec ℂ n × Vec ℂ n
  fac-parallel = parallel-result MF

  fac-mfp : Vec ℂ n × Vec ℂ n
  fac-mfp = mfp-result MF

module _ where
  open import While.Programs.Bogus-1
  private
    n : ℕ
    n = 7
    m : ℕ
    m = 3
    MF : MonotoneFramework Level.zero n
    MF = createMonotoneFramework n m bogus

  open MonotoneFramework.MonotoneFramework MF
  open BoundedSemiLattice L

  bogus-chaotic : Vec ℂ n × Vec ℂ n
  bogus-chaotic = chaotic-result MF

  bogus-parallel : Vec ℂ n × Vec ℂ n
  bogus-parallel = parallel-result MF

  bogus-mfp : Vec ℂ n × Vec ℂ n
  bogus-mfp = mfp-result MF


module _ where
  open import While.Programs.Bogus-2
  private
    n : ℕ
    n = 5
    m : ℕ
    m = 4
    MF : MonotoneFramework Level.zero n
    MF = createMonotoneFramework n m bogus₂

  open MonotoneFramework.MonotoneFramework MF
  open BoundedSemiLattice L

  bogus₂-chaotic : Vec ℂ n × Vec ℂ n
  bogus₂-chaotic = chaotic-result MF

  bogus₂-parallel : Vec ℂ n × Vec ℂ n
  bogus₂-parallel = parallel-result MF

  bogus₂-mfp : Vec ℂ n × Vec ℂ n
  bogus₂-mfp = mfp-result MF


module _ where
  open import While.Programs.Bogus-3
  private
    n : ℕ
    n = 5
    m : ℕ
    m = 3
    MF : MonotoneFramework Level.zero n
    MF = createMonotoneFramework n m bogus₃

  open MonotoneFramework.MonotoneFramework MF
  open BoundedSemiLattice L

  bogus₃-chaotic : Vec ℂ n × Vec ℂ n
  bogus₃-chaotic = chaotic-result MF

  bogus₃-parallel : Vec ℂ n × Vec ℂ n
  bogus₃-parallel = parallel-result MF

  bogus₃-mfp : Vec ℂ n × Vec ℂ n
  bogus₃-mfp = mfp-result MF
