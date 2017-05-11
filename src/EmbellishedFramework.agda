import Level
open import Agda.Builtin.Equality
open import Algebra.FunctionProperties
open import Coinduction
open import LatticeTheory
-- open import LatticeTheory.List
open import Data.Bool
open import Data.Fin
open import Data.Fin.Properties as FinP
open import Data.Fin.Subset
open import Data.Graph
open import Data.List
open import Data.List as 𝕃
open import Data.List.Any
open import Data.Maybe
open import Data.Nat hiding (_⊔_ ; _⊓_)
open import Data.Nat.Show
open import Data.Product
open import Data.String
open import Data.Vec
open import Data.Vec as 𝕍 hiding (head) 
open import ExtendedFramework
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse hiding (_∘_)
open import Function.Inverse using (_↔_)
open import MonotoneFramework
open import Monotonicity
open import Relation.Binary
open import Relation.Binary.List.Pointwise
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Util.BoundedList
open import Util.Subset
open import While-Fun.Language
open Labeled
module EmbellishedFramework where

data EmbellishedBlock (n : ℕ) : Set where
  other call : EmbellishedBlock n
  return : (c : Fin n) → EmbellishedBlock n

data Arity : Set where
  unary : Arity
  binary : Arity
  
arityArguments : ∀{a} → Arity → Set a → Set a
arityArguments unary ℂ = ℂ
arityArguments binary ℂ = ℂ × ℂ

arityToType : ∀{a} → Arity → Set a → Set a
arityToType unary ℂ = ℂ → ℂ
arityToType binary ℂ = ℂ → ℂ → ℂ

arity : ∀{n} → (Fin n → EmbellishedBlock n) → Fin n → Arity
arity f x with f x
arity f x | return c = binary
arity f x | _ = unary

module EmbellishedFrameworkMonotonicity {a} (n : ℕ) (L : BoundedSemiLattice a) (open BoundedSemiLattice L) (arity : Fin n → Arity) (𝓕 : (ℓ : Fin n) -> arityToType (arity ℓ) ℂ) where
  Monotonicity : Fin n → Set a
  Monotonicity ℓ with arity ℓ | 𝓕 ℓ
  Monotonicity ℓ | unary | r = Monotone _⊑_ r
  Monotonicity ℓ | binary | r = BiMonotone _⊑_ r

record EmbellishedMonotoneFramework a : Set (Level.suc a) where
  field
    n : ℕ
    L : BoundedSemiLattice a -- Lattice instance
  Label : Set
  Label = Fin n
  field
    k : ℕ
    labelType : Label → EmbellishedBlock n
    𝓕 : (ℓ : Label) -> arityToType (arity labelType ℓ) (BoundedSemiLattice.ℂ L)
    E : List Label    -- Extremal labels                               
    ι : BoundedSemiLattice.ℂ L                -- Extremal value
  open EmbellishedFrameworkMonotonicity n L (arity labelType) 𝓕
  field
    𝓕-isMonotone : (ℓ : Fin n) → Monotonicity ℓ

  Δ : Set
  Δ = BoundedList (Fin n) k

  BoundedList↔′ : Σ[ r ∈ ℕ ] Δ ↔ Fin r
  BoundedList↔′ = isBijectiveToFin (n , Function.Inverse.id) 

  r : ℕ
  r = proj₁ BoundedList↔′

  BoundedList↔ : Δ ↔ Fin r
  BoundedList↔ = proj₂ BoundedList↔′

  L̂ : BoundedSemiLattice a
  L̂ = Δ -[ BoundedList↔′ ]→ L

  module L̂ where
    open BoundedSemiLattice L̂ public
  module L where
    open BoundedSemiLattice L public
  open BoundedSemiLattice L̂

  allCallStrings≤k : List Δ
  allCallStrings≤k = 𝕃.map (λ i → Inverse.from (BoundedList↔) ⟨$⟩ i) (𝕍.toList (allFin r))

  𝓕̂ : Fin n → ℂ → ℂ
  𝓕̂ ℓ l̂ δ′ with labelType ℓ | 𝓕 ℓ
  𝓕̂ ℓ l̂ δ′ | other | f = f (l̂ δ′)
  𝓕̂ ℓ l̂ δ′ | call | f = f (L.⨆ (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then l̂ δ else L.⊥ ) allCallStrings≤k )) 
  𝓕̂ ℓ l̂ δ′ | return ℓc | f = f (l̂ δ′) (l̂ (cons ℓc δ′)) 

  ι̂ : ℂ
  ι̂ (zero , nil) = ι
  ι̂ (suc n₁ , cons' x xs x₁) = L.⊥


  𝓕̂-isMonotone : (ℓ : Fin n) → Monotone _⊑_ (𝓕̂ ℓ)
  𝓕̂-isMonotone ℓ {x} {y} with labelType ℓ | 𝓕 ℓ | 𝓕-isMonotone ℓ
  𝓕̂-isMonotone ℓ {x} {y}  | other | 𝓕′ | m = λ x⊑y → $-⊑' Δ BoundedList↔′ L (λ z → 𝓕′ (x z)) (λ z → 𝓕′ (y z)) (λ δ′ → m ($-⊑ Δ BoundedList↔′ L x y δ′ x⊑y))
  𝓕̂-isMonotone ℓ {x} {y}  | call | 𝓕′ | m = λ x⊑y →
    $-⊑' Δ BoundedList↔′ L (λ δ′ → 𝓕′ (L.⨆ (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then x δ else L.⊥) allCallStrings≤k )))
                           (λ δ′ → 𝓕′ (L.⨆ (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then y δ else L.⊥) allCallStrings≤k)))
      (λ δ′ → m (L.⨆⊑⨆-pointwise (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then x δ else L.⊥) allCallStrings≤k)
                                  (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then y δ else L.⊥) allCallStrings≤k)
               (rec (λ {v₁} {v₂} x₁ → Relation.Binary.List.Pointwise.Rel L._⊑_ (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then x δ else L.⊥) v₁) (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then y δ else L.⊥) v₂))
                 (λ {x′} {y′} {xs′} {ys′} {xs′≡ys′} x∼y x₂ → g δ′ x∼y x⊑y Relation.Binary.List.Pointwise.∷ x₂) [] (≡⇒Rel≡ (_≡_.refl {_} {_} {allCallStrings≤k}))))) 
     where g : ∀{x′ y′ x y} (δ′ : Δ) → x′ ≡ y′ → x ⊑ y → (Data.Bool.if ⌊ Util.BoundedList.decidable-≡ FinP._≟_ (cons ℓ x′) δ′ ⌋ then x x′ else L.⊥)
                                        L.⊑ (Data.Bool.if ⌊ Util.BoundedList.decidable-≡ FinP._≟_ (cons ℓ y′) δ′ ⌋ then y y′ else L.⊥)
           g {x′} {.x′} {x} {y} δ′ _≡_.refl x₃ with ⌊ Util.BoundedList.decidable-≡ FinP._≟_ (cons ℓ x′) δ′ ⌋
           ... | true = $-⊑ Δ BoundedList↔′ L x y x′ x₃
           ... | false = L.⊔-idem (Data.Bool.if false then x x′ else L.⊥)
  𝓕̂-isMonotone ℓ {x} {y}  | return c | 𝓕′ | m = λ x⊑y → $-⊑' Δ BoundedList↔′ L (λ z → 𝓕′ (x z) (x (cons c z))) (λ z → 𝓕′ (y z) (y (cons c z))) (λ δ′ → m ($-⊑ Δ BoundedList↔′ L x y δ′ x⊑y) ($-⊑ Δ BoundedList↔′ L x y (cons c δ′) x⊑y))


  asMonotoneFramework : (F : Graph n) → MonotoneFramework a
  asMonotoneFramework F = record
              { n = n
              ; L = L̂
              ; 𝓕 = 𝓕̂
              ; F = F
              ; E = E
              ; ι = ι̂
              ; 𝓕-isMonotone = 𝓕̂-isMonotone
              }


  open ProductEncoding
  open Containment {Level.zero} {n * n} {Fin n × Fin n} (ℕ×ℕ↔ℕ n) 
  asExtendedFramework : (next : Label → ℂ → Subset (n * n)) → ((ℓ : Fin n) → Monotone₂ _⊑_ (BoundedSemiLattice._⊑_ (𝓟ᴸ-by-inclusion (n * n))) (next ℓ)) → ExtendedFramework a
  asExtendedFramework next next-mono =
    record
    { n = n
    ; L = L̂
    ; 𝓕 = 𝓕̂
    ; next = next
    ; E = E
    ; ι = ι̂
    ; 𝓕-isMonotone = 𝓕̂-isMonotone
    ; next-isMonotone = next-mono
    }

  showEmb : (showL : L.ℂ → String) → L̂.ℂ → String
  showEmb showL x = "{" Data.String.++ Data.String.fromList (𝕃.concat (intersperse (Data.String.toList "; ") (𝕍.toList (𝕍.map (λ δ → Data.String.toList (showBL (Data.Nat.Show.show ∘ toℕ) (Inverse.from BoundedList↔ ⟨$⟩ δ) Data.String.++ " ⟶ " Data.String.++ showL (x (Inverse.from BoundedList↔ ⟨$⟩ δ)))) (allFin r))))) Data.String.++ "}"



{-
module UnaryVersion {a} (n : ℕ)
               (L : BoundedSemiLattice a) (k : ℕ)
               (𝓕 : Fin n → BoundedSemiLattice.ℂ L → BoundedSemiLattice.ℂ L)
               (F : Graph n)
               (E : List (Fin n))
               (ι : BoundedSemiLattice.ℂ L)
               (𝓕-isMonotone : (ℓ : Fin n) → Monotone (BoundedSemiLattice._⊑_ L) (𝓕 ℓ))
               (labelType : Fin n → EmbellishedBlock n)
               where

  Δ : Set
  Δ = BoundedList (Fin n) k

  BoundedList↔ : Σ[ n ∈ ℕ ] Δ ↔ Fin n
  BoundedList↔ = isBijectiveToFin (n , Function.Inverse.id)

  L̂ : BoundedSemiLattice a
  L̂ = Δ -[ BoundedList↔ ]→ L


  module L where
    open BoundedSemiLattice L public
  open BoundedSemiLattice L̂

  allCallStrings≤k : List Δ
  allCallStrings≤k = 𝕃.map (λ i → Inverse.from (proj₂ BoundedList↔) ⟨$⟩ i) (𝕍.toList (allFin (proj₁ BoundedList↔)))

  open import Relation.Binary.List.Pointwise
  open import Function
  𝓕̂ : Fin n → ℂ → ℂ
  𝓕̂ ℓ l̂ δ′ with labelType ℓ
  𝓕̂ ℓ l̂ δ′ | other = 𝓕 ℓ (l̂ δ′)
  𝓕̂ ℓ l̂ δ′ | call = L.⨆ (𝕃.map (λ δ → Data.Bool.if ⌊ cons ℓ δ ≟⟨ FinP._≟_ ⟩ δ′ ⌋ then l̂ δ else L.⊥ ) allCallStrings≤k )
  𝓕̂ ℓ l̂ δ′ | return ℓc = 𝓕 ℓ (l̂ (cons ℓc δ′)) 

  ι̂ : ℂ
  ι̂ (zero , nil) = ι
  ι̂ (suc n₁ , cons' x xs x₁) = L.⊥ 

  embellish : MonotoneFramework a
  embellish = record
              { n = n
              ; L = L̂
              ; 𝓕 = 𝓕̂
              ; F = F
              ; E = E
              ; ι = ι̂
              ; 𝓕-isMonotone = 𝓕̂-isMonotone
              }
-}




    {-
    MonotoneFramework.n example = n
    MonotoneFramework.L example = BoundedList (Fin n) k -[ {!!} , {!!} ]→ L
    MonotoneFramework.𝓕 example = {!!}
    MonotoneFramework.F example = {!!}
    MonotoneFramework.E example = {!!}
    MonotoneFramework.ι example = {!!}
    MonotoneFramework.𝓕-isMonotone example = {!!}
    -}
--  open MonotoneFramework.MonotoneFramework mf
--
{-
Transfer functie hangt af van label.
dus type van lab aanpassen:

data Lab : Set where
  intra : Fin n → Lab
  inter : Fin n → Lab

type van transfer functie is nu:

Lab → TransferResult Lab

waar:
TransferResult : Lab → Set
TransferResult (intra l) = ℂ → ℂ
TransferResult (inter l) = ℂ → ℂ → ℂ


maar: bij forward analyse heeft   return   twee argumenten
          bij backward    heeft   call     twee argumenten   


het type van Edge is afhankelijk van Lab..

Edge : Lab → Set
Edge (intra l) = Fin n × Fin n
Edge (inter l) = Fin n × Fin n × Fin n × Fin n

Edge = Σ[ ℓ ∈ Fin n ] (
-----------------------------------------------------------
of we hebben een functie die bepaalt wat voor flow een block heeft.

Lab = Fin n

data FlowType : Set where
  intra : FlowType
  inter : FlowType

flowType : Lab → FlowType
flowType = -- AG

TransferResult : Lab → Set
TransferResult l with flowType l
TransferResult l | intra = ℂ → ℂ
TransferResult l | inter = ℂ → ℂ → ℂ

transfer-function : (ℓ : Lab) → TransferResult ℓ


successor : Lab → Set
successor ℓ with flowType l
successor ℓ | intra = Lab
successor ℓ | inter = Lab × Lab × Lab

-- maar we willen bij Return mergen...

Edge : Set
Edge = Σ[ ℓ ∈ Lab ] successor ℓ

maar...     nu ook MFP aanpassen.
            want nu ook andere labels.
-----------------------------------------------------------------

Embellished monotone frameworks hebben transfer functies die af kunnen hangen van twee elementen. Deze functies zijn dus binair en zijn niet slechts opgebouwd uit de join van de twee
argumenten.
In ons geval bij de while language hebben we enkel te maken met unaire en binaire functies. Maar je kunt je voorstellen dat er ook
problemen zijn waarbij we meer dan twee argumenten in de transfer functie krijgen.





this does not work: (we dont know what type of set the following should be contained in)
record Example1 : Set where
    field
      n : ℕ
      f : N-ary n ℕ ℕ
-}



{-
  record Example4 {a} (n : ℕ) (k : ℕ) : Set (N-ary-level a a n Level.⊔ Level.suc a) where
    field
      L : BoundedSemiLattice a
      f : Fin n → Σ[ m ∈ Fin k ] N-ary n (BoundedSemiLattice.ℂ L) (BoundedSemiLattice.ℂ L)

nu lopen we tegen een probleem aan, namelijk dat we niet weten hoe groot de set is
in principe zou je zeggen dat: we weten n; we weten dus ook alle elementen Fin n; dus we kunnen
arity erover mappen en dan de join/max ervan nemen?
-}
{-
  module WithDependentFlowGraph where
    open import NAryFlow hiding (Arity)
    open import Function
    open import Relation.Binary.PropositionalEquality
  
    module EmbellishedFrameworkExtra {a} (n : ℕ) (L : BoundedSemiLattice a) (open BoundedSemiLattice L) (arity : Fin n → Arity) (𝓕 : (ℓ : Fin n) -> arityToType (arity ℓ) ℂ) where
      Monotonicity : Fin n → Set a
      Monotonicity ℓ with arity ℓ | 𝓕 ℓ
      Monotonicity ℓ | unary | r = Monotone _⊑_ r
      Monotonicity ℓ | binary | r = BiMonotone _⊑_ r
  
    record EmbellishedFramework a : Set (Level.suc a) where
      field
        n : ℕ
        L : BoundedSemiLattice a -- Lattice instance

      open BoundedSemiLattice L -- public
      Label : Set
      Label = Fin n
      field
        arity : Fin n → Arity

      field
        𝓕 : (ℓ : Label) -> arityToType (arity ℓ) ℂ
      open EmbellishedFrameworkExtra n L arity 𝓕
      field
        𝓕-isMonotone : (ℓ : Label) → Monotonicity ℓ
      field
        F : List (NAryFlow.Edge n arity)     -- Control flow graph
        E : List Label    -- Extremal labels                               
        ι : ℂ             -- Extremal value


    module Algorithm-MFP {a} (mf : EmbellishedFramework a) where
      open EmbellishedFramework mf
      open BoundedSemiLattice L 
      open Reasoning
      private
        module V where
          open BoundedSemiLattice (Vecᴸ L n) public
          open BoundedSemiLattice.Reasoning (Vecᴸ L n) public

      open import Data.Fin.Dec
      open import Data.Fin.Properties as FinP

      {-# TERMINATING #-}
      mfp : (x : V.ℂ) → (workList : List (NAryFlow.Edge n arity)) → V.ℂ
      mfp x [] = x
      mfp x ((ℓ′ , ℓs) ∷ y) with arity ℓ′ | 𝓕 ℓ′
      mfp x ((ℓ′ , ℓ) ∷ y) | unary | f with f (lookup ℓ x) ⊑? lookup ℓ′ x
      mfp x ((ℓ′ , ℓ) ∷ y) | unary | f | yes p = mfp x y
      mfp x ((ℓ′ , ℓ) ∷ y) | unary | f | no ¬p = mfp (x [ ℓ′ ]≔ f (lookup ℓ x) ⊔ lookup ℓ′ x) (NAryFlow.outgoing n arity F ℓ′ 𝕃.++ y)
      mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ y) | binary | f with f (lookup ℓ₁ x) (lookup ℓ₂ x) ⊑? lookup ℓ′ x
      mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ y) | binary | f | yes p = mfp x y
      mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ y) | binary | f | no ¬p = mfp (x [ ℓ′ ]≔ f (lookup ℓ₁ x) (lookup ℓ₂ x) ⊔ lookup ℓ′ x) (NAryFlow.outgoing n arity F ℓ′ 𝕃.++ y)
-}

















    {-
    mfp x ((ℓ , p) ∷ l) with arity ℓ | 𝓕 ℓ
    mfp x ((ℓ′ , ℓ₁) ∷ l) | unary | f with f (lookup ℓ₁ x) ⊑? lookup ℓ′ x
    mfp x ((ℓ′ , ℓ₁) ∷ l) | unary | f | yes p = mfp x l
    mfp x ((ℓ′ , ℓ₁) ∷ l) | unary | f | no ¬p = mfp (x [ ℓ′ ]≔ f (lookup ℓ₁ x) ⊔ lookup ℓ′ x) ({!!} 𝕃.++ l) 
    mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ l) | binary | f with f (lookup ℓ₁ x) (lookup ℓ₂ x) ⊑? lookup ℓ′ x
    mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ l) | binary | f | yes p = mfp x l
    mfp x ((ℓ′ , ℓ₁ , ℓ₂) ∷ l) | binary | f | no ¬p = mfp (x [ ℓ′ ]≔ f (lookup ℓ₁ x) (lookup ℓ₂ x) ⊔ lookup ℓ′ x) ({!!} 𝕃.++ l)
    -}
    {-
    mfp x [] = x
    mfp x ((ℓ , ℓ′) ∷ worklist) with 𝑓 ℓ x ⊑? lookup ℓ′ x 
    mfp x ((ℓ , ℓ′) ∷ worklist) | yes p = mfp x worklist
    mfp x ((ℓ , ℓ′) ∷ worklist) | no ¬p = mfp (x [ ℓ′ ]≔ 𝑓 ℓ x ⊔ lookup ℓ′ x) (outgoing f ℓ′ 𝕃.++ worklist)

  open import completelattice
  g : embellishedframework _
  g = record
        { n = 2
        ; l = boolᴸ
        ; arity = λ{ zero → unary ; (suc zero) → binary ; (suc (suc ()))}
        ; 𝓕 = λ{ zero → function.id ; (suc zero) → λ x x₁ → x ; (suc (suc ()))}
        ; 𝓕-ismonotone = λ{ zero → λ x → x ; (suc zero) → λ x x₁ → x ; (suc (suc ()))}
        ; f = ?-- ((# 0) , (# 1))  ∷ ((# 1) , ((# 0) , (# 1))) ∷ []
        ; e = []
        ; ι = false
        }
        -}

    {-
      Δ : Set d
      bij : Σ[ n ∈ ℕ ] Δ ↔ Fin n
      monotoneFramework : MonotoneFramework a 
      IF : List (Fin n) × (Fin n) × (Fin n) × (Fin n)
    open MonotoneFramework.MonotoneFramework monotoneFramework
    -}



{-
    private
      asMonotoneFramework : MonotoneFramework (a Level.⊔ d) n
      MonotoneFramework.L asMonotoneFramework = Δ -[ bij ]→ L
      MonotoneFramework.𝓕 asMonotoneFramework ℓ l̂ δ = 𝓕 ℓ (l̂ δ)
      MonotoneFramework.F asMonotoneFramework = flow⋆ labelledProgram
      MonotoneFramework.E asMonotoneFramework = final⋆ labelledProgram
      MonotoneFramework.ι asMonotoneFramework = {!!}
      MonotoneFramework.𝓕-isMonotone asMonotoneFramework = {!!}
    open MonotoneFramework.MonotoneFramework asMonotoneFramework public renaming (L to L̂ ; 𝓕 to 𝓕̂ ; 𝑓 to 𝑓̂ ; ι to ι̂ ; E to Ê ; F to F̂ ; 𝓕-isMonotone to 𝓕̂-isMonotone)
-}
{-
    open WhileProgram whileProgram
    open Extra whileProgram
(whileProgram : WhileProgram)
  emb : MonotoneFramework _ _
  MonotoneFramework.L emb = Δ -[ bij ]→ L
  MonotoneFramework.𝓕 emb ℓ l̂ δ = 𝓕 ℓ (l̂ δ)
  MonotoneFramework.F emb = flow⋆ labelledProgram
  MonotoneFramework.E emb = final⋆ labelledProgram
  MonotoneFramework.ι emb δ = ι
  MonotoneFramework.𝓕-isMonotone emb = {!!}
-}
{-
  record MonotoneFramework a (n : ℕ) : Set (Level.suc a) where
    field
      L : BoundedSemiLattice a -- Lattice instance
    open BoundedSemiLattice L -- public
    Label : Set
    Label = Fin n
    field
      𝓕 : Label -> ℂ -> ℂ  -- Set of transfer functions indexed by label   --todo monotonicity constraint
      F : Graph n          -- Control flow graph
      E : List⁺ Label    -- Extremal labels                               
      ι : ℂ                -- Extremal value
      𝓕-isMonotone : (ℓ : Fin n) → Monotone _⊑_ (𝓕 ℓ)

    𝑓 : Label → Vec ℂ n → ℂ
    𝑓 ℓ x = 𝓕 ℓ (lookup ℓ x)


    ιE : Label → ℂ
    ιE ℓ′ = if ⌊ Data.List.Any.any (FinP._≟ ℓ′) (𝕃⁺.toList E) ⌋
          then ι
          else ⊥







-----------------------------------------------------------------------------

we willen ℂ × ℂ   op plekken van binaire transfer functie.


het komt erop neer dat we many-to-one edges aan de flow graph willen toevoegen.

ipv Edge = Lab × Lab
->  Edge = (target : Lab) → predecessors target
waar predecessors = Lab⁺

Daarnaast zijn de transfer functies nu afhankelijk van het label, (de ariteit).

het kan dus zijn dat 𝓕 0 : ℂ → ℂ
              en dat 𝓕 1 : ℂ → ℂ → ℂ
              en dat 𝓕 2 : ℂ → ℂ → ℂ → ℂ → ℂ

Stel dat we dit omvormen naar:
                     𝓕 0 : ℂ → ℂ
                     𝓕 1 : ℂ × ℂ → ℂ
                     𝓕 2 : ℂ × ℂ × ℂ × ℂ → ℂ


zodat nu toch alle transfer functies unair zijn.
Het is alleen wel zo dat tussen de transfer functies het domein verschilt.
De monotonie eis veranderd dus.

Oorspronkelijk was deze:  (ℓ : Fin n) → x ⊑ y -> 𝓕 ℓ x ⊑ 𝓕 ℓ y 

Dat zou dan worden:   (ℓ : Fin n) → x ⊑ₙ y → 𝓕 ℓ x ⊑ 𝓕 ℓ y      (waar ⊑ₙ nu voor elke label anders kan zijn; maar is altijd een ⊑ van een product)


Stel anders:
     𝓕 0 : N-ary ℂ 1 → ℂ
     𝓕 1 : N-ary ℂ 2 → ℂ
     
nodig:

  functie die arity bepaald voor label
  monotone met twee domeinen.

maarja,..

















Oke,

Het probleem waar we nu tegen aanlopen:

Extended monotone frameworks:
  voegt een functie toe :   next : Label → ℂ → [(Label, Label, Label, Label)]
  de functie next geeft per block een potentieel nieuwe verzameling van control flow edges.
  













wat wil ik persoonlijk:


Stel L₁ en L₂ zijn een lattice.
Dan weten we dat ook L = L₁ × L₂ een lattice.  (op een bepaalde manier)

We willen nu een soort van garantie, dat als
f monotoon is op L en een fixed point levert, dat ***
                       - er een functie g is die monotoon is zodat g : L₁ → L₁ en ook een fixed point.






stel f : L → L

x is een fix point van f zodat: f x ≡ x
f is monotoon:  x ⊑ y ⇒ f x ⊑ f y




we beginnen van ⊥ =  (ι , [volledige worklist?])   →  (⊥ , ⊥)



uiteindelijk hebben we een punt x zodat  x = (y, z)       
                                  en  f (y , z) ≡ (y , z)

we begonnen vanaf ⊥ = (⊥ , ⊥).

dus: (f ∘ ⋯ ∘ f) (⊥ , ⊥)  ≡ f (y , z) ≡ (y , z)


We willen nu een eigenschap formuleren over een product dat zegt:

stel (y , z) is een fix point onder f vanaf ⊥.
dan bestaat er dus een serie (⊥, r₁ , r₂ , r₃ , ⋯  , z) ∈ [L₂]  zodat

  f ∘ ⋯ ∘ f (⊥ , ⊥)  ≡  (g z ∘ ⋯ ∘ g r₂ ∘ g r₁ ∘ g ⊥) ⊥ ≡ g z y ≡ y 


dan is y een fixpoint voor g z : L₁ → L₁    g = ...

maar, wat we eigenlijk willen is van alle verschillende g, een functie h maken zodat:

  (h ∘  ⋯ ∘ h) ⊥ ≡ h y ≡ y





MFP als monotone functie op (L₁ × L₂) =






( L is dependent product :    ( x : L₁) × (L₂ x)


-)   Stel we beginnen niet met de volledige worklist, hoe weten we dan dat alles in de worklist heeft gezeten?


 -}


