
module README where


-- Listable sets and listable subsets
open import Finiteness
-- The example of a straightforward approach of defining new finite
-- type Pauli and some operations on it.
open import Examples.Pauli


-- Basic combinators on listable sets and subsets
open import Combinators
-- Simple example of using combinators
open import Examples.Combinators


-- Pragmatic way of defining new sets as a subsets of some base set
-- with decidable equality
open import FiniteSubset
-- The alternative way of defining the new finite sets as a subsets
-- of a base set with decidable equality
open import Examples.FiniteSubset


-- Defining new functions from finite sets by providing an explicit
-- table + proofs of correctness
open import Tabulation
-- Example of a function definition by using tables
open import Examples.Tabulation


-- Defining new functions from the list of predicate--function pairs
-- and proofs of correctness
open import PredicateMatching
-- Examples
open import Examples.PredicateMatching


-- Prover for propositions quantified over finite sets
open import Prover
-- Comapring the approaches of automatically deriving the properties
-- for finite types
open import Examples.Prover

