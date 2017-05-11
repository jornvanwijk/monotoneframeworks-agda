open import Data.String hiding (_++_ ; setoid)
open import Data.Nat
open import Function
open import Relation.Unary
open import Relation.Nullary
open import Relation.Nullary.Sum renaming (_⊎-dec_ to _⋁-dec_)
open import Relation.Nullary.Product renaming (_×-dec_ to _⋀-dec_)
open import Relation.Nullary.Decidable 
open import Relation.Nullary.Implication
open import Relation.Nullary.Negation
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.List
open import Data.Sum renaming (_⊎_ to _⋁_)
open import Data.Fin renaming (_+_ to _fin+_)
open import Data.Integer hiding (suc)

module While-Fun-old.Language (n : ℕ) (m : ℕ) where    
  Var : Set
  Var = Fin m

  data AExpr : Set where
    var : Var → AExpr
    lit : ℤ → AExpr
    _plus_ : AExpr → AExpr → AExpr
    _min_ : AExpr → AExpr → AExpr
    _mul_ : AExpr → AExpr → AExpr
    
  data BExpr : Set where
    true : BExpr
    false : BExpr
    not : BExpr → BExpr
    _and_ : BExpr → BExpr → BExpr
    _or_ : BExpr → BExpr → BExpr
    _gt_ : AExpr → AExpr → BExpr

  open import Relation.Binary
  open import Data.Product
  open import Relation.Nullary.Product
  open import Data.Fin.Properties

  _≟A_ : Relation.Binary.Decidable {A = AExpr} _≡_
  var x ≟A var x₁ with x Data.Fin.Properties.≟ x₁
  var x ≟A var x₁ | yes p = yes (cong var p)
  var x ≟A var x₁ | no ¬p = no (λ{ refl → ¬p refl})
  var x ≟A lit x₁ = no (λ{ ()})
  var x ≟A (y plus y₁) = no (λ{ ()})
  var x ≟A (y min y₁) = no (λ{ ()})
  var x ≟A (y mul y₁) = no (λ{ ()})
  lit x ≟A var x₁ = no (λ{ ()})
  lit x ≟A lit x₁ with x Data.Integer.≟ x₁
  lit x ≟A lit x₁ | yes p = yes (cong lit p)
  lit x ≟A lit x₁ | no ¬p = no (λ{ refl → ¬p refl})
  lit x ≟A (y plus y₁) = no (λ{ ()})
  lit x ≟A (y min y₁) = no (λ{ ()})
  lit x ≟A (y mul y₁) = no (λ{ ()})
  (x plus x₁) ≟A var x₂ = no (λ{ ()})
  (x plus x₁) ≟A lit x₂ = no (λ{ ()})
  (x plus x₁) ≟A (y plus y₁) with x ≟A y ×-dec x₁ ≟A y₁
  (x plus x₁) ≟A (y plus y₁) | yes (proj₁ , proj₂) = yes (cong₂ _plus_ proj₁ proj₂)
  (x plus x₁) ≟A (y plus y₁) | no ¬p = no (λ{ refl → ¬p (refl , refl)})
  (x plus x₁) ≟A (y min y₁) = no (λ{ ()})
  (x plus x₁) ≟A (y mul y₁) = no (λ{ ()})
  (x min x₁) ≟A var x₂ = no (λ{ ()})
  (x min x₁) ≟A lit x₂ = no (λ{ ()})
  (x min x₁) ≟A (y plus y₁) = no (λ{ ()})
  (x min x₁) ≟A (y min y₁) with x ≟A y ×-dec x₁ ≟A y₁
  (x min x₁) ≟A (y min y₁) | yes (proj₁ , proj₂) = yes (cong₂ _min_ proj₁ proj₂)
  (x min x₁) ≟A (y min y₁) | no ¬p = no (λ{ refl → ¬p (refl , refl)})
  (x min x₁) ≟A (y mul y₁) = no (λ{ ()})
  (x mul x₁) ≟A var x₂ = no (λ{ ()})
  (x mul x₁) ≟A lit x₂ = no (λ{ ()})
  (x mul x₁) ≟A (y plus y₁) = no (λ{ ()})
  (x mul x₁) ≟A (y min y₁) = no (λ{ ()})
  (x mul x₁) ≟A (y mul y₁) with x ≟A y ×-dec x₁ ≟A y₁
  (x mul x₁) ≟A (y mul y₁) | yes (proj₁ , proj₂) = yes (cong₂ _mul_ proj₁ proj₂)
  (x mul x₁) ≟A (y mul y₁) | no ¬p = no (λ{ refl → ¬p (refl , refl)})


  _≟B_ : Relation.Binary.Decidable {A = BExpr} _≡_
  true ≟B true = yes refl
  true ≟B false = no (λ{ ()})
  true ≟B not y = no (λ{ ()})
  true ≟B (y and y₁) = no (λ{ ()})
  true ≟B (y or y₁) = no (λ{ ()})
  true ≟B (x gt x₁) = no (λ{ ()})
  false ≟B true = no (λ{ ()})
  false ≟B false = yes refl
  false ≟B not y = no (λ{ ()})
  false ≟B (y and y₁) = no (λ{ ()})
  false ≟B (y or y₁) = no (λ{ ()})
  false ≟B (x gt x₁) =  no (λ{ ()})
  not x ≟B true =  no (λ{ ()})
  not x ≟B false =  no (λ{ ()})
  not x ≟B not y with x ≟B y
  not x ≟B not y | yes p = yes (cong not p)
  not x ≟B not y | no ¬p = no (λ{ refl → ¬p refl})
  not x ≟B (y and y₁) =  no (λ{ ()})
  not x ≟B (y or y₁) =  no (λ{ ()})
  not x ≟B (x₁ gt x₂) =  no (λ{ ()})
  (x and x₁) ≟B true = no (λ{ ()})
  (x and x₁) ≟B false = no (λ{ ()})
  (x and x₁) ≟B not y = no (λ{ ()})
  (x and x₁) ≟B (y and y₁) with x ≟B y | x₁ ≟B y₁
  (x and x₁) ≟B (y and y₁) | yes p | yes p₁ = yes (cong₂ _and_ p p₁)
  (x and x₁) ≟B (y and y₁) | no ¬p | yes p =  no (λ{ refl → ¬p refl})
  (x and x₁) ≟B (y and y₁) | yes p | no ¬p =  no (λ{ refl → ¬p refl})
  (x and x₁) ≟B (y and y₁) | no ¬p | no ¬p₁ = no (λ{ refl → ¬p refl})
  (x and x₁) ≟B (y or y₁) = no (λ{ ()})
  (x and x₁) ≟B (x₂ gt x₃) = no (λ{ ()})
  (x or x₁) ≟B true =  no (λ{ ()})
  (x or x₁) ≟B false =  no (λ{ ()})
  (x or x₁) ≟B not y =  no (λ{ ()})
  (x or x₁) ≟B (y and y₁) =  no (λ{ ()})
  (x or x₁) ≟B (y or y₁) with x ≟B y ×-dec x₁ ≟B y₁
  (x or x₁) ≟B (y or y₁) | yes (proj₁ , proj₂) = yes (cong₂ _or_ proj₁ proj₂)
  (x or x₁) ≟B (y or y₁) | no ¬p = no (λ{ refl → ¬p (refl , refl)})
  (x or x₁) ≟B (x₂ gt x₃) =  no (λ{ ()})
  (x gt x₁) ≟B true =  no (λ{ ()})
  (x gt x₁) ≟B false =  no (λ{ ()})
  (x gt x₁) ≟B not y =  no (λ{ ()})
  (x gt x₁) ≟B (y and y₁) =  no (λ{ ()})
  (x gt x₁) ≟B (y or y₁) =  no (λ{ ()})
  (x gt x₁) ≟B (x₂ gt x₃) with x ≟A x₂ ×-dec x₁ ≟A x₃
  (x gt x₁) ≟B (x₂ gt x₃) | yes (proj₁ , proj₂) = yes (cong₂ _gt_ proj₁ proj₂)
  (x gt x₁) ≟B (x₂ gt x₃) | no ¬p = no (λ{ refl → ¬p ((refl , refl))})


  
  infixr 50 _seq_
  infixr 60 while_do_
  infix 70 _:=_
  infix 71 _mul_ {- todo: correct fixity -}
  infix 71 _min_ {- todo: . -}

  open import Data.Sum
  {-
  Lab : Set
  Lab = Fin n ⊎ (Fin n × Fin n)
  -}
  
  data LabType : Set where
    single : LabType
    double : LabType

  data Lab : LabType → Set where
    single : Fin n → Lab single
    double : Fin n → Fin n → Lab double

  Lab₁ : Set
  Lab₁ = Lab single
  Lab₂ : Set
  Lab₂ = Lab double


  data Stmt : Set where
    _:=_ : (v : Var) → (e : AExpr) → (l : Lab₁) → Stmt
    skip : (l : Lab₁) → Stmt
    _seq_ : (s₁ : Stmt) → (s₂ : Stmt) → Stmt
    if_then_else_ : (BExpr × Lab₁) → (t : Stmt) → (f : Stmt) → Stmt
    while_do_ : (BExpr × Lab₁) → (b : Stmt) → Stmt
    call : (name : String) → (arguments : List AExpr) → (result : Var) → (call : Lab₁) → (ret : Lab₁) → Stmt

  data Decl : Set where
    proc_⟨_,_⟩_is_end_ : (name : String) → (arguments : List Var) → (result : Var) → (entry : Lab₁) → (body : Stmt) → (exit : Lab₁) → Decl

  data Program : Set where
    begin_main-is_end : (declarations : List Decl) → (main : Stmt) → Program

  postulate
    _≟S_ : Relation.Binary.Decidable {A = Stmt} _≡_

  Var*-AExpr : AExpr → List Var
  Var*-AExpr (var x) = [ x ]
  Var*-AExpr (lit x) = []
  Var*-AExpr (a plus a₁) = Var*-AExpr a ++ Var*-AExpr a₁
  Var*-AExpr (a min a₁) = Var*-AExpr a ++ Var*-AExpr a₁
  Var*-AExpr (a mul a₁) = Var*-AExpr a ++ Var*-AExpr a₁
  
  Var*-BExpr : BExpr → List Var
  Var*-BExpr true = []
  Var*-BExpr false = []
  Var*-BExpr (not b) = []
  Var*-BExpr (b and b₁) = []
  Var*-BExpr (b or b₁) = []
  Var*-BExpr (x gt x₁) = Var*-AExpr x ++ Var*-AExpr x₁

  Var* : Stmt → List Var
  Var* ((v := e) l) = v ∷ Var*-AExpr e
  Var* (skip l) = []
  Var* (s seq s₁) = Var* s ++ Var* s₁
  Var* (if proj₁ , proj₂ then s else s₁) = Var*-BExpr proj₁ ++ Var* s ++ Var* s₁
  Var* (while proj₁ , proj₂ do s) = Var*-BExpr proj₁ ++ Var* s
  Var* (call f as r c ret) = r ∷ (concat ∘ Data.List.map Var*-AExpr) as

    
 

  {-
  Var*' : AExpr → Pred Var Level.zero
  Var*' (var x₁) v₁ = x₁ ≡ v₁
  Var*' (lit x₁) v₁ = ⊥
  Var*' (a plus a₁) v₁ = v₁ ∈ (Var*' a ∪ Var*' a₁)
  Var*' (a min a₁) v₁ =  v₁ ∈ (Var*' a ∪ Var*' a₁)
  Var*' (a mul a₁) v₁ = v₁ ∈ (Var*' a ∪ Var*' a₁)
                                              
                                              
  Var* : Stmt → Pred Var Level.zero
  Var* ((i := x) l) v = i ≡ v ⋁ v ∈ Var*' x
  Var* (skip x) v = ⊥
  Var* (s seq s₁) v = v ∈ (Var* s ∪ Var* s₁)
  Var* (if c , l then t else f) v = v ∈ (Var* t ∪ Var* f)
  Var* (while c , l do s) v = Var* s v

  Var*'-dec : (expr : AExpr) → Decidable (Var*' expr)
  Var*'-dec (var x) v = x Data.String.≟ v
  Var*'-dec (lit x) v = no (λ x₁ → x₁)
  Var*'-dec (x plus x₁) v = Var*'-dec x v ⋁-dec Var*'-dec x₁ v
  Var*'-dec (x min x₁) v = Var*'-dec x v ⋁-dec Var*'-dec x₁ v
  Var*'-dec (x mul x₁) v = Var*'-dec x v ⋁-dec Var*'-dec x₁ v
  
  Var*-dec : (program : Stmt) → Decidable (Var* program)
  Var*-dec ((x := x₁) x₂) x₃ = x Data.String.≟ x₃ ⋁-dec Var*'-dec x₁ x₃
  Var*-dec (skip x) x₁ = no (λ z → z)
  Var*-dec (program seq program₁) x = Var*-dec program x ⋁-dec Var*-dec program₁ x
  Var*-dec (if x then program else program₁) x₁ = Var*-dec program x₁ ⋁-dec Var*-dec program₁ x₁
  Var*-dec (while x do program) x₁ =  Var*-dec program x₁
  -}

  init : Stmt → Lab₁
  init ((v := e) l) = l
  init (skip x) = x
  init (s seq s₁) = init s
  init (if proj₁ , proj₂ then s else s₁) = proj₂
  init (while proj₁ , proj₂ do s) = proj₂
  init (call f as r c ret) = c

  import Data.List.NonEmpty as L⁺
  final : Stmt → L⁺.List⁺ Lab₁
  final ((v := e) l) = L⁺.[ l ]
  final (skip l) = L⁺.[ l ]
  final (s seq s₁) = final s₁
  final (if proj₁ , proj₂ then s else s₁) = final s L⁺.⁺++⁺ final s₁
  final (while proj₁ , proj₂ do s) = L⁺.[ proj₂ ]
  final (call f as r c ret) = L⁺.[ ret ]


  data Block : Set where
    skip : (l : Lab₁) → Block
    _:=_ : (x : Var) → (a : AExpr) → (l : Lab₁) → Block
    bExpr : (c : BExpr) → (l : Lab₁) → Block
    call : (name : String) → (arguments : List AExpr) → (result : Var) → (call : Lab₁) → (ret : Lab₁) → Block
    is : (l : Lab₁) → Block
    end : (l : Lab₁) → Block

  -- we want this function to be: Stmt → Vec Block n
  -- but, we dont have proof that every label is present in the code.
  blocks : Stmt → List Block
  blocks ((v := e) l) = [ (v := e) l ]
  blocks (skip l) = [ skip l ]
  blocks (s seq s₁) = blocks s ++ blocks s₁
  blocks (if proj₁ , proj₂ then s else s₁) = bExpr proj₁ proj₂ ∷ blocks s ++ blocks s₁
  blocks (while proj₁ , proj₂ do s) = bExpr proj₁ proj₂ ∷ blocks s
  blocks (call f as r c ret) = [ call f as r c ret ]
  
  -- but a quicker and dirtier solution is to use this function
  getLab₁ : Block → Lab₁
  getLab₁ (skip l) = l
  getLab₁ ((x := a) l) = l
  getLab₁ (bExpr c l) = l
  getLab₁ (call f as r c ret) = c -- ?
  getLab₁ (is l) = l
  getLab₁ (end l) = l
 
  labels : Stmt → List Lab₁
  labels ((v := e) l) = [ l ]
  labels (skip l) = [ l ]
  labels (s seq s₁) = labels s Data.List.++ labels s₁
  labels (if x then s else s₁) = proj₂ x ∷ labels s Data.List.++ labels s₁
  labels (while x do s) = proj₂ x ∷ labels s
  labels (call f as r c ret) = c ∷ ret ∷ []

  open import Data.List.Any
  open Membership-≡
  flow : Program → Stmt → List (Lab₁ × Lab₁)
  flow p ((v := e) l) = []
  flow p (skip l) = []
  flow p (s seq s₁) = flow p s ++ flow p s₁ ++ L⁺.toList (L⁺.map (λ x → x , init s₁) (final s)) 
  flow p (if x then s else s₁) = ((proj₂ x) , (init s)) ∷ ((proj₂ x) , (init s₁)) ∷ flow p s ++ flow p s₁
  flow p (while x do s) = ((proj₂ x) , (init s)) ∷ flow p s ++ L⁺.toList (L⁺.map (λ l' → l' , proj₂ x) (final s))
  flow (begin declarations main-is main end) (call f as r c ret) = g (proj₁ (find q))
    where postulate
           q : Any (λ{ (proc name ⟨ arguments , result ⟩ entry is body end exit) → name ≡ f}) declarations
          g : Decl → List (Lab₁ × Lab₁)
          g (proc name ⟨ arguments , result ⟩ entry is body end exit) = (c , entry) ∷ (exit , ret) ∷ []

  init⋆ : Program → Lab₁
  init⋆ (begin declarations main-is main end) = init main

  final⋆ : Program → L⁺.List⁺ Lab₁
  final⋆ begin declarations main-is main end = final main


  blocks⋆ : Program → List Block
  blocks⋆ begin declarations main-is main end = blocks main ++ (concat ∘ Data.List.map (λ{ (proc name ⟨ arguments , result ⟩ entry is body end exit) → is entry ∷ end exit ∷  blocks body})) declarations 

  labels⋆ : Program → List Lab₁
  labels⋆ begin declarations main-is main end = labels main ++ (concat ∘ Data.List.map (λ{ (proc name ⟨ arguments , result ⟩ entry is body end exit) → entry ∷ exit ∷ labels body})) declarations

  flow⋆ : Program → List (Lab₁ × Lab₁)
  flow⋆ p@(begin declarations main-is main end) = flow p main ++ (concat ∘ Data.List.map (λ{ (proc name ⟨ arguments , result ⟩ entry is body end exit) → (entry , (init body)) ∷ (L⁺.toList (L⁺.map (_, exit) (final body)) ++ flow p body)})) declarations

  inter-flow⋆ : Program → List (Lab₁ × Lab₁ × Lab₁ × Lab₁)
  inter-flow⋆ p@(begin declarations main-is main end) = g main
   where g : Stmt → List (Lab₁ × Lab₁ × Lab₁ × Lab₁)
         g ((v := e) l) = []
         g (skip l) = []
         g (s seq s₁) = g s ++ g s₁
         g (if x then s else s₁) = g s ++ g s₁
         g (while x do s) = g s
         g (call f arguments result c ret) = h (proj₁ (find q))
           where postulate
                  q : Any (λ{ (proc name ⟨ arguments , result ⟩ entry is body end exit) → name ≡ f}) declarations
                 h : Decl → List (Lab₁ × Lab₁ × Lab₁ × Lab₁)
                 h (proc name ⟨ arguments₁ , result₁ ⟩ entry is body end exit) = (c , entry , exit , ret) ∷ []

  open import Data.Graph n
