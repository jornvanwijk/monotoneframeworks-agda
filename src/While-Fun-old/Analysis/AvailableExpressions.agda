open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.Graph 6
open import MonotoneFramework as MF
import Data.List.NonEmpty
open import Data.Fin.Subset
import Level
open import LatticeTheory
--open import Data.Vec hiding (init)
open import Data.Nat hiding (_≟_)
open import Data.Fin.Properties
open import Relation.Nullary
open import Algorithms
open import Function
--open import Data.Vec
open import Data.List
open import Monotonicity

module While.Analysis.AvailableExpressions (n : ℕ) (m : ℕ) where
  open import While.Language n m

    {-
  data ASubExpr⋆ : AExpr → Set where
    _plus_ : (a : AExpr) → (b : AExpr) → ASubExpr⋆ (a plus b)
    _min_ : (a : AExpr) → (b : AExpr) → ASubExpr⋆ (a min b)
    _mul_ : (a : AExpr) → (b : AExpr) → ASubExpr⋆ (a mul b)


  AExprToℕ : AExpr -> ℕ
  AExprToℕ (var x) = 19 ^ (toℕ x)
  AExprToℕ (lit x) = 17 ^ x
  AExprToℕ (x plus y) = 11 ^ (AExprToℕ x) * 13 ^ (AExprToℕ y)
  AExprToℕ (x min y) = 7 ^ (AExprToℕ x) * 5 ^ (AExprToℕ y)
  AExprToℕ (x mul y) = 2 ^ (AExprToℕ x) * 3 ^ (AExprToℕ y)

  open import Data.Nat.Divisibility
  open import Data.Bool hiding (_≟_)
  open import Relation.Nullary.Decidable
  ℕToAExpr : ℕ → AExpr
  ℕToAExpr zero = {!!}
  ℕToAExpr (suc n) with (suc n) ∣? 2
  ℕToAExpr (suc n) | yes (divides q p) = {!(ℕToAExpr q) mul ?!}
  ℕToAExpr (suc n) | no ¬q = {!q!}
  -}
  

  open import Data.List
  ASubExpr : Set
  ASubExpr = List AExpr

  subExpressions : AExpr → ASubExpr
  subExpressions (var x) = []
  subExpressions (lit x) = []
  subExpressions (x plus y) = x plus y ∷ subExpressions x ++ subExpressions y
  subExpressions (x min y) = x min y ∷ subExpressions x ++ subExpressions y
  subExpressions (x mul y) = x mul y ∷ subExpressions x ++ subExpressions y


  subExpressions-BExpr : BExpr → ASubExpr
  subExpressions-BExpr true = []
  subExpressions-BExpr false = []
  subExpressions-BExpr (not x) = subExpressions-BExpr x
  subExpressions-BExpr (x and y) = subExpressions-BExpr x ++ subExpressions-BExpr y
  subExpressions-BExpr (x or y) = subExpressions-BExpr x ++ subExpressions-BExpr y
  subExpressions-BExpr (x gt y) = subExpressions x ++ subExpressions y


  subExpressions-Stmt : Stmt → ASubExpr
  subExpressions-Stmt ((v := e) l) = subExpressions e
  subExpressions-Stmt (skip l) = []
  subExpressions-Stmt (x seq x₁) = subExpressions-Stmt x ++ subExpressions-Stmt x₁
  subExpressions-Stmt (if x then x₁ else x₂) = subExpressions-BExpr (proj₁ x) ++ subExpressions-Stmt x₁ ++ subExpressions-Stmt x₂
  subExpressions-Stmt (while x do x₁) = subExpressions-BExpr (proj₁ x) ++ subExpressions-Stmt x₁



  free-variables : AExpr → Subset m
  free-variables (var x) = ⁅ x ⁆
  free-variables (lit x) = ⊥
  free-variables (a plus a₁) = free-variables a ∪ free-variables a₁
  free-variables (a min a₁) = free-variables a ∪ free-variables a₁
  free-variables (a mul a₁) = free-variables a ∪ free-variables a₁



  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary

  
  module _ (program : Stmt) where
    AExpr⋆ : ASubExpr
    AExpr⋆ = subExpressions-Stmt program
    
    open import Data.List.Any renaming (module Membership-≡ to L)
    to : (a : AExpr) → Any (_≡ a) AExpr⋆ → Fin (length AExpr⋆)
    to a x = index x

   
    from : Fin (length AExpr⋆) → AExpr
    from x = f AExpr⋆ x
      where f : (xs : List AExpr) → Fin (length xs) → AExpr
            f [] ()
            f (x₁ ∷ xs) zero = x₁
            f (x₁ ∷ xs) (suc i) = f xs i

    open import Data.Vec hiding (init)
    open import Data.Fin.Dec
    open import Relation.Nullary.Decidable
    kill : Block → Subset (length AExpr⋆)
    kill (skip l) = ⊥
    kill ((x := a) l) = tabulate (λ i → ⌊ x ∈? free-variables (from i) ⌋)
    kill (bExpr c l) = ⊥
    open import Data.Bool
    gen : Block → Subset (length AExpr⋆)
    gen (skip l) = ⊥
    gen ((x := a) l) = tabulate (λ i →  ⌊ Data.List.Any.any (_≟A (from i)) (subExpressions a) ⌋ ∧ Data.Bool.not ⌊ x ∈? free-variables (from i) ⌋)
    gen (bExpr c l) = tabulate (λ i → ⌊ Data.List.Any.any (_≟A (from i)) (subExpressions-BExpr c) ⌋)

    _-_ : ∀{n} → Subset n → Subset n → Subset n
    x - y = x ∩ (∁ y)


    transfer-function : Block → Lab → Subset (length AExpr⋆) → Subset (length AExpr⋆)
    transfer-function b l₁ x with (getLab b) Data.Fin.Properties.≟ l₁
    transfer-function b l₁ x | yes p = (x - (kill b)) ∪ gen b
    transfer-function b l₁ x | no ¬p = x
  
    -- very inefficient; reason @ WhileLanguage.Blocks
    transfer-functions : Lab → Subset (length AExpr⋆) → Subset (length AExpr⋆)
    transfer-functions l x = Data.List.foldr (flip transfer-function l) x (blocks program)

    postulate
      transfer-monotone : (ℓ : Fin n) → Monotone (BoundedSemiLattice._⊑_ (Vecᴸ Mustᴸ (length AExpr⋆))) (transfer-functions ℓ)

    open import Data.List.NonEmpty hiding (length)
    available-expressions : MonotoneFramework _ _
    available-expressions = record
         { L = Vecᴸ Mustᴸ (length AExpr⋆)
         ; 𝓕 = transfer-functions
         ; F = flow program
         ; E = Data.List.NonEmpty.[ init program ]
         ; ι = ⊥
         ; 𝓕-isMonotone = transfer-monotone
         }
{-

  we kunnen een lijst maken van de sub expressies voor een programma.
  Vervolgens, zouden we duplicaten kunnen verwijderen.
  We kunnen dan een mapping maken van elementen in deze lijst naar Fin n.

  Daarna, kunnen we een subset maken van Fin n die zegt of element n erin zit ja of nee.

  We hebben dan een conversie functie nodig die een willekeurige Expr omzet naar een Fin n.
  






  divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n

  divides {suc n} {2} q p
                      suc n ∣ 2

  data AExpr : Set where
  19   var : Var → AExpr
  17   lit : ℕ → AExpr
  11 13   _plus_ : AExpr → AExpr → AExpr
  5 7   _min_ : AExpr → AExpr → AExpr
  2 3   _mul_ : AExpr → AExpr → AExpr

    
  data BExpr : Set where
    true : BExpr
    false : BExpr
    not : BExpr → BExpr
    _and_ : BExpr → BExpr → BExpr
    _or_ : BExpr → BExpr → BExpr
    _gt_ : AExpr → AExpr → BExpr

-}


{-
 version without subset but using a list without guarantee that there is an upperbound for the subset 
  open import Data.Vec
  kill : Block → ASubExpr → ASubExpr
  kill (skip l) xs = []
  kill ((x := a) l) xs = filter (λ y → lookup x (free-variables y)) xs
  kill (bExpr c l) xs = []


  free-variables-BExpr : BExpr → Subset m
  free-variables-BExpr true = ⊥
  free-variables-BExpr false = ⊥
  free-variables-BExpr (not b) = free-variables-BExpr b
  free-variables-BExpr (b and b₁) = free-variables-BExpr b ∪ free-variables-BExpr b₁
  free-variables-BExpr (b or b₁) =  free-variables-BExpr b ∪ free-variables-BExpr b₁
  free-variables-BExpr (x gt x₁) = free-variables x ∪ free-variables x₁

  import Data.Bool as 𝔹
  open 𝔹 using (not)
  gen : Block → ASubExpr → ASubExpr
  gen (skip l) x₁ = []
  gen ((x := a) l) x₁ = filter (λ y → 𝔹.not (lookup x (free-variables y))) (subExpressions a)
  gen (bExpr c l) x₁ = subExpressions-BExpr c


  transfer-function : Block → Lab → ASubExpr → ASubExpr
  transfer-function b l₁ x with (getLab b) ≟ l₁
  transfer-function b l₁ x | yes p = (kill b (gen b x)) 
  transfer-function b l₁ x | no ¬p = x
  
  -- very inefficient; reason @ WhileLanguage.Blocks
  transfer-functions : Stmt → Lab → ASubExpr → ASubExpr
  transfer-functions p l x = Data.List.foldr (flip transfer-function l) x (blocks p)
-}

