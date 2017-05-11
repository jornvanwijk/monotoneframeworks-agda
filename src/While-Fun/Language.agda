open import Data.String hiding (_++_ ; setoid)
open import Data.Nat
open import Function
--open import Relation.Unary
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
open import Data.Integer
open import Util.Bag hiding ([])
open import Util.List
open import Data.Vec using (Vec)
open import Data.String using (String)

module While-Fun.Language where




    


  module Common where

    infix 73 _mul_ {- todo: correct fixity -}
    infix 71 _plus_ {- todo: correct fixity -}
    infixl 72 _min_ {- todo: . -}
    data AExpr {a} (Ident : Set a) : Set a where
      var : Ident → AExpr Ident
      lit : ℤ → AExpr  Ident
      _plus_ : AExpr Ident → AExpr Ident → AExpr Ident
      _min_ : AExpr Ident → AExpr Ident → AExpr Ident
      _mul_ : AExpr Ident → AExpr Ident → AExpr Ident

    infixr 30 _and_
    data BExpr {a} (Ident : Set a) : Set a where
      true : BExpr Ident
      false : BExpr Ident
      not : BExpr Ident → BExpr Ident
      _and_ : BExpr Ident → BExpr Ident → BExpr Ident
      _or_ : BExpr Ident → BExpr Ident → BExpr Ident
      _gt_ : AExpr Ident → AExpr Ident → BExpr Ident

   
    record AExpr-Algebra {a} (Ident : Set a) (A : Set a) : Set a where
 --     constructor AExpr-Algebra*
      field
        var* : (x : Ident) → A
        lit* : (z : ℤ) → A
        _plus*_ : (x : A) → (y : A) → A
        _min*_ : (x : A) → (y : A) → A
        _mul*_ : (x : A) → (y : A) → A

    record BExpr-Algebra {a} (Ident : Set a) (A : Set a) (B : Set a) : Set a where
--      constructor BExpr-Algebra*
      field
        aExprAlg : AExpr-Algebra Ident A
        true* : B
        false* : B
        not* : (x : B) → B
        _and*_ : (x : B) → (y : B) → B
        _or*_ : (x : B) → (y : B) → B
        _gt*_ : (x : A) → (y : A) → B

    foldAExpr : ∀{a} → {Ident : Set a} → {A : Set a} → AExpr-Algebra Ident A → AExpr Ident → A
    foldAExpr {Ident = Ident} {A} record { var* = var* ; lit* = lit* ; _plus*_ = _plus*_ ; _min*_ = _min*_ ; _mul*_ = _mul*_ } e = f e
     where f : AExpr Ident → A
           f (var x) = var* x  -- P (var x)
           f (lit x) = lit* x
           f (e₁ plus e₂) = f e₁ plus* f e₂
           f (e₁ min e₂) = f e₁ min* f e₂
           f (e₁ mul e₂) = f e₁ mul* f e₂

    foldBExpr : ∀{a} → {Ident : Set a} → {A : Set a} → {B : Set a} → BExpr-Algebra Ident A B → BExpr Ident → B
    foldBExpr {Ident = Ident} {A} {B} record { aExprAlg = aExprAlg ; true* = true* ; false* = false* ; not* = not* ; _and*_ = _and*_ ; _or*_ = _or*_ ; _gt*_ = _gt*_ } e = f e
     where f : BExpr Ident → B
           f true = true*
           f false = false*
           f (not e₁) = not* $ f e₁
           f (e₁ and e₂) = f e₁ and* f e₂
           f (e₁ or e₂) = f e₁ or* f e₂
           f (x gt x₁) = foldAExpr aExprAlg x gt* foldAExpr aExprAlg x₁
    
  module Unlabeled where

    AExpr : Set
    AExpr = Common.AExpr {Level.zero} String
    
    BExpr : Set
    BExpr = Common.BExpr {Level.zero} String
  
    open Common hiding (AExpr ; BExpr) public
    
    infixr 50 _seq_
    infixr 60 while_do_
    infix 70 _:=_
    open import Data.String
    data Stmt : Set where
      _:=_ : (v : String) → (e : AExpr) → Stmt
      skip :  Stmt
      _seq_ : (s₁ : Stmt) → (s₂ : Stmt) → Stmt
      if_then_else_ : (c : BExpr) → (t : Stmt) → (f : Stmt) → Stmt
      while_do_ : (c : BExpr) → (b : Stmt) → Stmt
      call : (name : String) → (arguments : List AExpr) → (result : String) → Stmt

    
    record Stmt-Algebra (A : Set) (B : Set) (C : Set) : Set where
      field
        bExprAlg : BExpr-Algebra String A B
        _:=*_ : (v : String) → (e : A) → C
        skip* : C
        _seq*_ : (l : C) → (r : C) → C
        if*_then_else_ : (c : B) → (t : C) → (f : C) → C
        while*_do_ : (c : B) → (b : C) → C
        call* : (n : String) → (a : List A) → (r : String) → C
    
    foldStmt : {A B C : Set} → Stmt-Algebra A B C → Stmt → C
    foldStmt {A} {B} {C} record { bExprAlg = bExprAlg ; _:=*_ = _:=*_ ; skip* = skip* ; _seq*_ = _seq*_ ; if*_then_else_ = if*_then_else_ ; while*_do_ = while*_do_ ; call* = call*} e = f e
     where f : Stmt → C
           f (v := e₁) = v :=* foldAExpr (BExpr-Algebra.aExprAlg bExprAlg) e₁
           f skip = skip*
           f (s seq s₁) = f s seq* f s₁
           f (if c then s else s₁) = if* foldBExpr bExprAlg c then f s else f s₁
           f (while c do s) = while* foldBExpr bExprAlg c do f s
           f (call name arguments result) = call* name (Data.List.map (foldAExpr (BExpr-Algebra.aExprAlg bExprAlg)) arguments) result

    data Decl : Set where
      proc_⟨_,_⟩_end : (name : String) → (arguments : List String) → (result : String) → (body : Stmt) → Decl

    record Decl-Algebra (A : Set) (B : Set) (C : Set) (D : Set) : Set where
      field
        stmtAlg : Stmt-Algebra A B C
        proc*_⟨_,_⟩_end : String → List String → String → C → D

    foldDecl : {A B C D : Set} → Decl-Algebra A B C D → Decl → D
    foldDecl {A} {B} {C} {D} record { stmtAlg = stmtAlg ; proc*_⟨_,_⟩_end = proc*_⟨_,_⟩_end } e = f e
      where f : Decl → D
            f proc name ⟨ arguments , result ⟩ body end = proc* name ⟨ arguments , result ⟩ foldStmt stmtAlg body end

    data Program : Set where
      begin_main-is_end : (declarations : List Decl) → (main : Stmt) → Program

    record Program-Algebra (A : Set) (B : Set) (C : Set) (D : Set) (E : Set) : Set where
      field
        declAlg : Decl-Algebra A B C D
        begin*_main-is_end : List D → C → E
    
    foldProgram : {A B C D E : Set} → Program-Algebra A B C D E → Program → E
    foldProgram {E = E} record { declAlg = declAlg ; begin*_main-is_end = begin*_main-is_end } e = f e
      where f : Program → E
            f begin declarations main-is main end = begin* Data.List.map (foldDecl declAlg) declarations main-is foldStmt (Decl-Algebra.stmtAlg declAlg) main end
    
  module Labeled where
    
    open Common hiding (AExpr ; BExpr) public
    open Unlabeled hiding (AExpr ; BExpr ; Stmt ; Decl ; Program)
    open Stmt-Algebra
    open Common.BExpr-Algebra
    open Common.AExpr-Algebra
    open import Data.Fin
    open import Data.Product
    module 𝕍 where
      open import Data.Vec public
    open import Data.Vec using (_∷_ ; Vec)
    open import Relation.Binary
    open import Data.Product
    open import Relation.Nullary.Product
    open import Data.Fin.Properties
    open import Data.List.Any
    open Membership-≡
    open import Data.Nat.Properties
    
    infixr 50 _seq_
    infixr 60 while_do_
    infix 70 _:=_

{-

    data LabType : Set where
      assignment : LabType
      skip : LabType
      condition : LabType
      call : LabType
      exit : LabType
      return : LabType
      entry : LabType

    data Label (n : ℕ) : LabType → Set where
      assignment : (Fin n) → Label n assignment
      skip : (Fin n) → Label n skip
      condition : (Fin n) → Label n condition
      call : (Fin n) → Label n call
      exit : (Fin n) → Label n exit
      return : (Fin n) → Label n return
      entry : (Fin n) → Label n entry

    data Stmt' {a} {b} {c} (Lab : LabType → Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c) where
      _:=_ : (v : Var) → (e : Common.AExpr Var) → (l : Lab assignment) → Stmt' Lab Var Fun
      skip : (l : Lab skip) → Stmt' Lab Var Fun
      _seq_ : (s₁ : Stmt' Lab Var Fun) → (s₂ : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      if_then_else_ : (Common.BExpr Var × Lab condition) → (t : Stmt' Lab Var Fun) → (f : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      while_do_ : (Common.BExpr Var × Lab condition) → (b : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      call : (c : Lab call) → (name : Fun) → (r : Lab return) → (a : List (Common.AExpr Var)) → (r : Var) → Stmt' Lab Var Fun

    data Block' {a} {b} {c} (Lab : LabType → Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      skip : (l : Lab skip) → Block' Lab Var Fun
      _:=_ : (x : Var) → (a : Common.AExpr Var) → (l : Lab assignment) → Block' Lab Var Fun
      bExpr : (c : Common.BExpr Var) → (l : Lab condition) → Block' Lab Var Fun
      call : (c : Lab call) → (name : Fun) → (r : Lab return) → (a : List (Common.AExpr Var)) → (r : Var) → Block' Lab Var Fun
      return : (c : Lab call) → (name : Fun) → (r : Lab return) → (a : List (Common.AExpr Var)) → (r : Var) → Block' Lab Var Fun
      entry : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab entry) → (body : Stmt' Lab Var Fun) → (exit : Lab exit) → Block' Lab Var Fun
      exit : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab entry) → (body : Stmt' Lab Var Fun) → (exit : Lab exit) → Block' Lab Var Fun
      -- is end

    data Decl' {a} {b} {c} (Lab : LabType → Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      proc_⟨_,_⟩_is_end_ : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab entry) → (body : Stmt' Lab Var Fun) → (exit : Lab exit) → Decl' Lab Var Fun
      
    data Program' {a} {b} {c} (Lab : LabType → Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      begin_main-is_end : (declarations : List (Decl' Lab Var Fun)) → (main : Stmt' Lab Var Fun) → Program' Lab Var Fun
      -}

    data Stmt' {a} {b} {c} (Lab : Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c) where
      _:=_ : (v : Var) → (e : Common.AExpr Var) → (l : Lab) → Stmt' Lab Var Fun
      skip : (l : Lab) → Stmt' Lab Var Fun
      _seq_ : (s₁ : Stmt' Lab Var Fun) → (s₂ : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      if_then_else_ : (Common.BExpr Var × Lab) → (t : Stmt' Lab Var Fun) → (f : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      while_do_ : (Common.BExpr Var × Lab) → (b : Stmt' Lab Var Fun) → Stmt' Lab Var Fun
      call : (c : Lab) → (name : Fun) → (r : Lab) → (a : List (Common.AExpr Var)) → (r : Var) → Stmt' Lab Var Fun

    data Block' {a} {b} {c} (Lab : Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      skip : (l : Lab) → Block' Lab Var Fun
      _:=_ : (x : Var) → (a : Common.AExpr Var) → (l : Lab) → Block' Lab Var Fun
      bExpr : (c : Common.BExpr Var) → (l : Lab ) → Block' Lab Var Fun
      call : (c : Lab) → (name : Fun) → (r : Lab) → (a : List (Common.AExpr Var)) → (r : Var) → Block' Lab Var Fun
      return : (c : Lab) → (name : Fun) → (r : Lab) → (a : List (Common.AExpr Var)) → (r : Var) → Block' Lab Var Fun
      entry : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab) → (body : Stmt' Lab Var Fun) → (exit : Lab) → Block' Lab Var Fun
      exit : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab) → (body : Stmt' Lab Var Fun) → (exit : Lab) → Block' Lab Var Fun
      -- is end

    data Decl' {a} {b} {c} (Lab : Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      proc_⟨_,_⟩_is_end_ : (name : Fun) → (arguments : List Var) → (result : Var) → (entry : Lab) → (body : Stmt' Lab Var Fun) → (exit : Lab) → Decl' Lab Var Fun
      
    data Program' {a} {b} {c} (Lab : Set a) (Var : Set b) (Fun : Set c) : Set (a Level.⊔ b Level.⊔ c)  where
      begin_main-is_end : (declarations : List (Decl' Lab Var Fun)) → (main : Stmt' Lab Var Fun) → Program' Lab Var Fun

    --open import NAryFlow
    record WhileProgram : Set₁ where
      field
        n : ℕ
        Var* : Bag String
        Fun* : Bag String
      m : ℕ
      m = length (Util.Bag.toList Var*)
      k : ℕ
      k = length (Util.Bag.toList Fun*)
      Lab : Set
      Lab = Fin n
      Var : Set
      Var = Fin m
      Fun : Set
      Fun = Fin k
      AExpr : Set
      AExpr = Common.AExpr Var
      BExpr : Set
      BExpr = Common.BExpr Var
      Stmt : Set
      Stmt = Stmt' Lab Var Fun
      Block : Set
      Block = Block' Lab Var Fun
      Decl : Set
      Decl = Decl' Lab Var Fun
      Program : Set
      Program = Program' Lab Var Fun
      field
        blocks : Vec Block n
        functions : Vec Decl k
        labelledProgram : Program
        
{-
  Omschrijving:

  Op de plek van 'return' labels kunnen binaire transfer functies komen, die iets doen met informatie van voor de function call (label: call) en na de call (label: exit).


  Elke transfer functie is gekoppeld aan een label, een label is een index voor een block. Een block is eigenlijk een abstractie van de taal.
  - waarom geen blocks voor: call, entry, exit en return.
  - waarom geen onderscheid maken tussen if en while.   (dit kan met AG bijvoorbeeld veel makkelijker)

  Stel wel blocks voor call,entry,exit en return
  dan kunnen we een datastructuur maken met precies deze knopen

    data EmbellishedLanguage {a} (Other : Set a) : Set a where
      other : Other → EmbellishedLanguage Other
      call return : ... → EmbellishedLanguage
      entry exit : ... → EmbellishedLanguage

  dan kunnen we voor een embellished analyse de transfer functies al geven voor call return exit en entry, zodat de gebruiker alleen voor Other de definities hoeft te geven.
  Daarnaast kunnen we de context met call strings toevoegen aan de lattice en k afhankelijk maken van een parameter. Aangezien de total function space combinator er al is hoeven we
  hiervoor alleen een bijectie aan te tonen met lijsten van hoogstens k elementen waarvan de elementen ook een bijectie met Fin n hebben en vervolgens de transfer functies invullen.


  Daarom eerst kijken naar de unaire/binaire transfer functies.

  Kunnen we de twee paden niet joinen?
    En eventueel de carrier aanpassen zodat we op elk punt weten (ongeveer) : Info voor een call; info na een call

  Plan:
    functie toevoegen die per label de ariteit bepaald. 
      arity : (Fin n = Lab) → Arity

  De flow graph bestaat dan ook uit many-to-one pijltjes.
  Deze zouden we ook weer kunnen omvormen naar one-to-one pijltjes, maar dan is het domein van de lattice afhankelijk van de index

  dan krijgen we bijvoorbeeld:
  Vec (heterogeen) 2
  0 : ℂ × ℂ
  1 : ℂ
  2 : ℂ × ℂ × ℂ

  Als we het op deze manier oplossen, dan blijft MFP volgens mij aardig hetzelfde. Alleen moet wel de eis toegevoegd worden dat de transfer functies met domain een product ook monotoon zijn.
  dus:
    Monotone _⊑_ f    (subset van indices)
    Monotone _⊑₁_ f    ..
    Monotone _⊑₂_ f    ..

  De andere mogelijkheid is om gewoon een functie aan het framework toe te voegen die ariteit bepaald aan de hand van een index en vervolgens
  de ariteit van de transfer functie; en de monotonie eis daarvan afhankelijk te maken:

    Monotonicity : Fin n → Set a
    Monotonicity ℓ with arity ℓ | 𝓕 ℓ
    Monotonicity ℓ | unary | r = Monotone _⊑_ r
    Monotonicity ℓ | binary | r = BiMonotone _⊑_ r

  en:

    𝓕 : (ℓ : Label) -> arityToType (arity ℓ) ℂ

  Dit lijkt me in principe een prima oplossing. Helaas loop ik dan tegen het volgende aan:
  Bij de definitie van de flow graph, zeggen we bij elke sequentie van statements dat de final van het linker statement naar de init van de rechter statement gaat.
  Dat is dus een unaire edge.

    flow (s seq s₁) = flow s ++ flow s₁ ++ Data.List.map (λ x → init s₁ , x) (final s)   -- edge van x naar init s₁    (volgorde omgekeerd; want dependent)


  dus bewijzen dat:  ∀ s : arity (init s) ≡ unary
  Dit geldt want alleen labels die naar blocks gaan van een return zijn binary en deze labels komen niet uit init:

    init : Stmt → Lab -- labelType ℓ ≡ unary
    init ((v := e) l) = l
    init (skip x) = x
    init (s seq s₁) = init s
    init (if proj₁ , proj₂ then s else s₁) = proj₂ 
    init (while proj₁ , proj₂ do s) = proj₂
    init (call c name r args result) = c

  Maar die informatie van blocks hebben we niet; want init is een functie van Stmt → Lab.
  Met andere woorden: we moeten nu voor elk statement het bewijs hebben dat deze correspondeerd met een bepaald block.

  

  
 
-}


  module Generated (program : Unlabeled.Stmt) where
    open Labeled
    
    open Common hiding (AExpr ; BExpr) public
    open Unlabeled hiding (AExpr ; BExpr ; Stmt)
    open Stmt-Algebra
    open Common.BExpr-Algebra
    open Common.AExpr-Algebra
    open Decl-Algebra
    open Program-Algebra
    open import Data.Fin
    open import Data.Product
    open import Data.Vec using (_∷_ ; Vec)
    open import Relation.Binary
    open import Data.Product
    open import Relation.Nullary.Product
    open import Data.Fin.Properties
    open import Data.List.Any
    open Membership-≡
    open import Data.Nat.Properties
    decrement-left : ∀{i j} → ℕ.suc i Data.Nat.≤ j → i Data.Nat.≤ j
    decrement-left (s≤s z≤n) = z≤n
    decrement-left (s≤s (s≤s p)) = s≤s (decrement-left (s≤s p))

{-
    -- algebra which computes several attributes in three visits
    -- visit-1  (left - to - right)
    -- AExpr BExpr Stmt inh      prevV : Bag String
                                 variables already encountered in the program; initially empty.
       Stmt inh                  prevL : ℕ
                                 amount of labels already given out to earlier blocks; initially 0.
       AExpr BExpr Stmt syn      curV : Bag String
                                 the set of variables in the program.

       Stmt syn                  curL : the amount of blocks/labels in the program.
       
       visit-2  (right - to - left)
       AExpr BExpr Stmt inh      allVariables : Bag String
                                 the set of all variables in the program
                                 pV : Util.Bag.toList curV ⊆ Util.Bag.toList allVariables
                                 the proof that the set of variables synthesized from this node is at most as big as the set of all variables
       Stmt inh                  pL : curL Data.Nat.≤ maxL
                                 the proof that the current label counter synthesized by this node is less or equal to the maximum
       AExpr BExpr Stmt syn      unnamed : Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables
                                 we must show it also holds for the set of variables we were given.
       AExpr syn                 unnamed : Common.AExpr (Fin (length (Util.Bag.toList allVariables)))
       BExpr syn                 unnamed : Common.BExpr (Fin (length (Util.Bag.toList allVariables)))
       Stmt  syn                 unnamed : Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))
       Stmt  syn                 unnamed : prevL Data.Nat.≤ maxL
            
       visit-3 (left-to-right)
       Stmt inh                  prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) prevL
                                 the vector of blocks already constructed
       Stmt syn                  unnamed : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) curL
      -}            
{-
    AExpr-Type : Set
    AExpr-Type = {- inh -} (prevV : Bag String) →
                 {- syn -}  Σ[ curV ∈ Bag String ]
                 {- inh -}   ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables →
                 {- syn -}    Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.AExpr (Fin (length (Util.Bag.toList allVariables))))

    BExpr-Type : Set
    BExpr-Type = ((prevV : Bag String) → Σ[ curV ∈ Bag String ] ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.BExpr (Fin (length (Util.Bag.toList allVariables)))))

    Stmt-Type : Set
    Stmt-Type = {- inh -} (prevL : ℕ) → (prevV : Bag String) → (allFunctions : Bag String) →
                {- syn -}  Σ[ curL ∈ ℕ ] Σ[ curV ∈ Bag String ] {- Σ[ curF ∈ Bag String ] -}
                {- inh -}   ((maxL : ℕ) → curL Data.Nat.≤ maxL →
                            (allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables →
                          {-  (allFunctions : Bag String) → Util.Bag.toList curF ⊆ Util.Bag.toList allFunctions → -}
                {- syn -}    Σ[ pL ∈ (prevL Data.Nat.≤ maxL) ]
                             Σ[ pV ∈ (Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables) ]
                          {- Σ[ pF ∈ (Util.Bag.toList prevF ⊆ Util.Bag.toList allFunctions) ] -}
                             Σ[ t ∈ Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables))) ]
                {- inh -}     ((prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables)))) prevL) → 
                {- syn -}      Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables)))) curL))

    Decl-Type : Set
    Decl-Type = {- inh -} (prevL : ℕ) → (prevV : Bag String) → {- (prevF : Bag String) → -}
                {- syn -}  Σ[ curL ∈ ℕ ] Σ[ curV ∈ Bag String ] {- Σ[ curF ∈ Bag String ] -}
                {- inh -}   ((maxL : ℕ) → curL Data.Nat.≤ maxL →
                            (allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables →
                          {-  (allFunctions : Bag String) → Util.Bag.toList curF ⊆ Util.Bag.toList allFunctions → -}
                {- syn -}    Σ[ pL ∈ (prevL Data.Nat.≤ maxL) ]
                             Σ[ pV ∈ (Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables) ]
                          {- Σ[ pF ∈ (Util.Bag.toList prevF ⊆ Util.Bag.toList allFunctions) ] -}
                             Σ[ t ∈ Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables))) ]
                {- inh -}     ((prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables)))) prevL) → 
                {- syn -}      Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin (length (Util.Bag.toList allVariables)))) curL))
    {-
    semAExpr : AExpr-Algebra String AExpr-Type
    var* semAExpr x (xs , nodup)  with x ∈?[ Data.String._≟_ ] xs
    var* semAExpr x (xs , nodup) | yes p = (xs , nodup) , (λ allVariables₁ x₁ → x₁ , (var (index (x₁ p))))
    var* semAExpr x (xs , nodup) | no ¬p = ((x ∷ xs) , (¬p ::: nodup)) , (λ allVariables₁ x₁ → (λ x₃ → x₁ (there x₃)) , var (index (x₁ (here refl)))) 
    lit* semAExpr z prevV = prevV , (λ allVariables₁ x → x , lit z)
    _plus*_ semAExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n plus l))
    _min*_ semAExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n min l))
    _mul*_ semAExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n mul l))

    semBExpr : BExpr-Algebra String AExpr-Type BExpr-Type
    aExprAlg semBExpr = semAExpr
    true* semBExpr prevV = prevV , (λ allVariables₁ x → x , true)
    false* semBExpr prevV = prevV , (λ allVariables₁ x → x , false)
    not* semBExpr x prevV =
      let (a , b) = x prevV
      in a , (λ allVariables₁ x₁ →
        let (c , d) = b allVariables₁ x₁
        in c , not d) 
    _and*_ semBExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_and_ n l))
    _or*_ semBExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_or_ n l))
    _gt*_ semBExpr x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_gt_ n l))
    -}
    
    semStmt : Stmt-Algebra AExpr-Type BExpr-Type Stmt-Type
    bExprAlg semStmt = {!!}
    _:=*_ semStmt x y prevL (xs , nodup) allFunctions with x ∈?[ Data.String._≟_ ] xs
    _:=*_ semStmt x y prevL (xs , nodup) allFunctions | yes p =
      let (yV , yF) = y (xs , nodup)
      in (ℕ.suc prevL) , yV  , (λ maxL x₁ allVariables₁ x₂ →
        let (yPV , yT) = yF allVariables₁ x₂  
        in (decrement-left x₁) , yPV , (index (yPV p) := yT) (fromℕ≤ x₁) , (λ prevBlock → prevBlock 𝕍.∷ʳ (index (yPV p) := yT) (fromℕ≤ x₁)))
    _:=*_ semStmt x y prevL (xs , nodup) allFunctions | no ¬p =
      let (yV , yF) = y (x ∷ xs , ¬p ::: nodup)
      in (ℕ.suc prevL) , yV , (λ maxL x₁ allVariables₁ x₂ →
        let (yPV , yT) = yF allVariables₁ x₂
        in decrement-left x₁ , (λ x₄ → yPV (there x₄)) , ((index (yPV (here refl)) := yT) (fromℕ≤ x₁) , (𝕍._∷ʳ (index (yPV (here refl)) := yT) (fromℕ≤ x₁)))) 
    skip* semStmt prevL prevV allFunctions = ℕ.suc prevL , prevV , (λ maxL x allVariables₁ x₁ → decrement-left x , x₁ , skip (fromℕ≤ x) , 𝕍._∷ʳ (skip (fromℕ≤ x)))
    _seq*_ semStmt x y prevL prevV allFunctions = 
      let (xL , xV , xF) = x prevL prevV allFunctions
          (yL , yV , yF) = y xL xV allFunctions
      in yL , yV , (λ maxL x₁ allVariables₁ x₂  →
        let (yPL , yPV , yT , yG) = yF maxL x₁ allVariables₁ x₂ 
            (xPL , xPV , xT , xG) = xF maxL yPL allVariables₁ yPV 
        in xPL , xPV , (xT seq yT) , (λ prevBlock →
          let xB = xG prevBlock
              yB = yG xB
          in yB))
    if*_then_else_ semStmt b t f prevL prevV allFunctions =
      let (bV , bF) = b prevV
          (tL , tV , tF) = t (ℕ.suc prevL) bV allFunctions
          (fL , fV , fF) = f tL tV allFunctions
      in fL , fV , (λ maxL x allVariables₁ x₁  →
        let (fPL , fPV , fT , fG) = fF maxL x allVariables₁ x₁ 
            (tPL , tPV , tT , tG) = tF maxL fPL allVariables₁ fPV 
            (bPV , bT) = bF allVariables₁ tPV 
        in decrement-left tPL , bPV , (if (bT , fromℕ≤ tPL) then tT else fT) , (λ prevBlock →
          let tB = tG (prevBlock 𝕍.∷ʳ bExpr bT (fromℕ≤ tPL))
              fB = fG tB
          in fB))
    while*_do_ semStmt c b prevL prevV allFunctions =
      let (cV , cF) = c prevV
          (bL , bV , bF) = b (ℕ.suc prevL) cV allFunctions
      in bL , bV , (λ maxL x allVariables₁ x₁ →
        let (bPL , bPV , bT , bG) = bF maxL x allVariables₁ x₁
            (cPV , cT) = cF allVariables₁ bPV
        in (decrement-left bPL) , cPV , (while (cT , fromℕ≤ bPL) do bT), (λ prevBlock → bG (prevBlock 𝕍.∷ʳ bExpr cT (fromℕ≤ bPL))))
    call* semStmt n a r prevL prevV allFunctions = {!!}

    semDecl : Decl-Algebra AExpr-Type BExpr-Type Stmt-Type Decl-Type
    stmtAlg semDecl = semStmt
    proc* semDecl ⟨ n , args ⟩ result end body prevL prevV = (ℕ.suc (ℕ.suc prevL)) , {!!} , (λ maxL x allVariables x₁ → (decrement-left (decrement-left x)) , {!!})
    
    semProgram : Program-Algebra AExpr-Type BExpr-Type Stmt-Type Decl-Type ℕ
    declAlg semProgram = {!!}
    begin*_main-is_end semProgram = {!!}

    sem : Program-Algebra ℕ ℕ ℕ ℕ ℕ
    bExprAlg (stmtAlg (declAlg sem)) = {!!}
    _:=*_ (stmtAlg (declAlg sem)) = {!!}
    skip* (stmtAlg (declAlg sem)) = {!!}
    _seq*_ (stmtAlg (declAlg sem)) = {!!}
    if*_then_else_ (stmtAlg (declAlg sem)) = {!!}
    while*_do_ (stmtAlg (declAlg sem)) = {!!}
    call* (stmtAlg (declAlg sem)) = {!!}
    proc*_⟨_,_⟩_end (declAlg sem) = {!!}
    begin*_main-is_end sem = {!!} 
-}


    {-
    sem : Program-Algebra
                 ((prevV : Bag String) → Σ[ curV ∈ Bag String ] ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.AExpr (Fin (length (Util.Bag.toList allVariables)))))
                 ((prevV : Bag String) → Σ[ curV ∈ Bag String ] ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.BExpr (Fin (length (Util.Bag.toList allVariables)))))
                 ((prevL : ℕ) → (prevV : Bag String) → Σ[ curL ∈ ℕ ] Σ[ curV ∈ Bag String ] ((maxL : ℕ) → curL Data.Nat.≤ maxL → (allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Σ[ pL ∈ (prevL Data.Nat.≤ maxL) ] Σ[ pV ∈ (Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables) ] Σ[ t ∈ Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin {!!}) ]
                 ((prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) prevL) → Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) curL)))
                 ((prevL : ℕ) → (prevV : Bag String) → Σ[ curL ∈ ℕ ] Σ[ curV ∈ Bag String ] ((maxL : ℕ) → curL Data.Nat.≤ maxL → (allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Σ[ pL ∈ (prevL Data.Nat.≤ maxL) ] Σ[ pV ∈ (Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables) ] Σ[ t ∈ Decl' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin {!!}) ]
                 ((prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) prevL) → Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) curL)))
                 {!!}
    var* (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x (xs , nodup) with x ∈?[ Data.String._≟_ ] xs
    var* (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x (xs , nodup) | yes p = (xs , nodup) , (λ allVariables₁ x₁ → x₁ , (var (index (x₁ p))))
    var* (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x (xs , nodup) | no ¬p = ((x ∷ xs) , (¬p ::: nodup)) , (λ allVariables₁ x₁ → (λ x₃ → x₁ (there x₃)) , var (index (x₁ (here refl)))) 
    lit* (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) z prevV = prevV , (λ allVariables₁ x → x , lit z)
    _plus*_ (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n plus l))
    _min*_ (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n min l))
    _mul*_ (aExprAlg (bExprAlg (stmtAlg (declAlg sem)))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (n mul l))
    true* (bExprAlg (stmtAlg (declAlg sem))) prevV = prevV , (λ allVariables₁ x → x , true)
    false* (bExprAlg (stmtAlg (declAlg sem))) prevV = prevV , (λ allVariables₁ x → x , false)
    not* (bExprAlg (stmtAlg (declAlg sem))) x prevV =
      let (a , b) = x prevV
      in a , (λ allVariables₁ x₁ →
        let (c , d) = b allVariables₁ x₁
        in c , not d) 
    _and*_ (bExprAlg (stmtAlg (declAlg sem))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_and_ n l))
    _or*_ (bExprAlg (stmtAlg (declAlg sem))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_or_ n l))
    _gt*_ (bExprAlg (stmtAlg (declAlg sem))) x y prevV =
      let (a , b) = x prevV
          (c , d) = y a
      in c , (λ allVariables x₁ →
        let (k , l) = d allVariables x₁
            (m , n) = b allVariables k
        in m , (_gt_ n l))
    _:=*_ (stmtAlg (declAlg sem)) x y prevL (xs , nodup) with x ∈?[ Data.String._≟_ ] xs
    _:=*_ (stmtAlg (declAlg sem)) x y prevL (xs , nodup) | yes p =
      let (yV , yF) = y (xs , nodup)
      in (ℕ.suc prevL) , (yV , (λ maxL x₁ allVariables₁ x₂ →
        let (yPV , yT) = yF allVariables₁ x₂ 
        in (decrement-left x₁) , yPV , (index (yPV p) := yT) (fromℕ≤ x₁) , (λ prevBlock → prevBlock 𝕍.∷ʳ (index (yPV p) := yT) (fromℕ≤ x₁))))
    _:=*_ (stmtAlg (declAlg sem)) x y prevL (xs , nodup) | no ¬p =
      let (yV , yF) = y (x ∷ xs , ¬p ::: nodup)
      in (ℕ.suc prevL) , (yV , (λ maxL x₁ allVariables₁ x₂ →
        let (yPV , yT) = yF allVariables₁ x₂
        in decrement-left x₁ , (λ x₄ → yPV (there x₄)) , ((index (yPV (here refl)) := yT) (fromℕ≤ x₁) , (𝕍._∷ʳ (index (yPV (here refl)) := yT) (fromℕ≤ x₁)))))
    skip* (stmtAlg (declAlg sem)) prevL prevV = ℕ.suc prevL , (prevV , (λ maxL x allVariables₁ x₁ → decrement-left x , (x₁ , skip (fromℕ≤ x) , 𝕍._∷ʳ (skip (fromℕ≤ x)))))
    _seq*_ (stmtAlg (declAlg sem)) x y prevL prevV =
      let (xL , xV , xF) = x prevL prevV
          (yL , yV , yF) = y xL xV
      in yL , (yV , (λ maxL x₁ allVariables₁ x₂ →
        let (yPL , yPV , yT , yG) = yF maxL x₁ allVariables₁ x₂ 
            (xPL , xPV , xT , xG) = xF maxL yPL allVariables₁ yPV
        in xPL , (xPV , (xT seq yT) , (λ prevBlock →
          let xB = xG prevBlock
              yB = yG xB
          in yB))))
    if*_then_else_ (stmtAlg (declAlg sem)) b t f prevL prevV =
      let (bV , bF) = b prevV
          (tL , tV , tF) = t (ℕ.suc prevL) bV
          (fL , fV , fF) = f tL tV
      in fL , (fV , (λ maxL x allVariables₁ x₁ →
        let (fPL , fPV , fT , fG) = fF maxL x allVariables₁ x₁ 
            (tPL , tPV , tT , tG) = tF maxL fPL allVariables₁ fPV 
            (bPV , bT) = bF allVariables₁ tPV 
        in decrement-left tPL , (bPV , (if (bT , fromℕ≤ tPL) then tT else fT) , (λ prevBlock →
          let tB = tG (prevBlock 𝕍.∷ʳ bExpr bT (fromℕ≤ tPL))
              fB = fG tB
          in fB))))
    while*_do_ (stmtAlg (declAlg sem)) c b prevL prevV =
      let (cV , cF) = c prevV
          (bL , bV , bF) = b (ℕ.suc prevL) cV
      in bL , (bV , (λ maxL x allVariables₁ x₁ →
        let (bPL , bPV , bT , bG) = bF maxL x allVariables₁ x₁ 
            (cPV , cT) = cF allVariables₁ bPV
        in (decrement-left bPL) , (cPV , (while (cT , fromℕ≤ bPL) do bT), (λ prevBlock → bG (prevBlock 𝕍.∷ʳ bExpr cT (fromℕ≤ bPL))))))
    call* (stmtAlg (declAlg sem)) n a r prevL prevV = {!!}
    proc* declAlg sem ⟨ x , x₁ ⟩ x₂ end x₃ prevL prevV = {!!}
    begin* sem main-is x end x₁ = {!!} 
                                                                                     
{-
    re : Σ[ maxL ∈ ℕ ] Σ[ allVariables ∈ Bag String ] Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) (Fin {!!}) × Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) maxL
    re = let (maxL , allVariables , f) = foldStmt example' program 0 ([] , end)
         in maxL , (allVariables , (let (pL , pV , pT , pG) = f maxL (≤′⇒≤ ≤′-refl) allVariables Function.id
                                    in pT , (pG Vec.[])))

    whileProgram : WhileProgram
    whileProgram = record
                     { n = proj₁ re
                     ; Var* = proj₁ (proj₂ re)
                     ; blocks = proj₂ (proj₂ (proj₂ re))
                     ; functions = {!!}
                     ; labelledProgram = {!!} -- proj₁ (proj₂ (proj₂ re))
                     }
  -}
  -}
  module Extra (open Labeled) (p : WhileProgram) where
    open WhileProgram p
    open Unlabeled hiding (AExpr ; BExpr ; Stmt ; Decl ; Program)
    open Stmt-Algebra
    open Common.BExpr-Algebra
    open Common.AExpr-Algebra
    open import Data.Fin
    open import Data.Product
    open import Data.Vec using (_∷_ ; Vec)
    open import Relation.Binary
    open import Data.Product
    open import Relation.Nullary.Product
    open import Data.Fin.Properties
    open import Data.List.Any
    open Membership-≡
    open import Data.Nat.Properties
    --open import NAryFlow

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

    open import Data.Graph n
    init : Stmt → Lab -- labelType ℓ ≡ unary
    init ((v := e) l) = l
    init (skip x) = x
    init (s seq s₁) = init s
    init (if proj₁ , proj₂ then s else s₁) = proj₂ 
    init (while proj₁ , proj₂ do s) = proj₂
    init (call c name r args result) = c

    final : Stmt → List Lab
    final ((v := e) l) = Data.List.[ l ]
    final (skip l) = Data.List.[ l ]
    final (s seq s₁) = final s₁
    final (if proj₁ , proj₂ then s else s₁) = final s Data.List.++ final s₁
    final (while proj₁ , proj₂ do s) = Data.List.[ proj₂ ]
    final (call c name r args result) = Data.List.[ r ]

  
    flow : Stmt → List Edge
    flow ((v := e) l) = []
    flow (skip l) = []
    flow (s seq s₁) = flow s ++ flow s₁ ++ Data.List.map (λ x → x , init s₁) (final s)
    flow (if x then s else s₁) = (proj₂ x , init s) ∷ (proj₂ x , init s₁) ∷ flow s ++ flow s₁
    flow (while x do s) = (proj₂ x , init s) ∷ flow s ++ Data.List.map (λ x₁ → x₁ , proj₂ x) (final s)
    flow (call c name r a r₁) = g (Data.Vec.lookup name functions)
       where g : Decl → List Edge
             g (proc name₁ ⟨ arguments , result₁ ⟩ n is body end x) = (c , n) ∷ (x , r) ∷ [] --(unary , n , c) ∷ (binary , r , c , x) ∷ []
  

    open import Data.String
    show-Var : Var → String
    show-Var v = Data.Vec.lookup v (Data.Vec.fromList (proj₁ Var*))
    
    show-Fun : Fun → String
    show-Fun v = Data.Vec.lookup v (Data.Vec.fromList (proj₁ Fun*))
    
    show-AExpr : AExpr → String
    show-AExpr (var x) = show-Var x
    show-AExpr (lit x) = Data.Integer.show x
    show-AExpr (a plus a₁) = show-AExpr a Data.String.++ " plus " Data.String.++ show-AExpr a₁
    show-AExpr (a min a₁) = show-AExpr a Data.String.++ " min " Data.String.++ show-AExpr a₁
    show-AExpr (a mul a₁) = show-AExpr a Data.String.++ " mul " Data.String.++ show-AExpr a₁

    show-BExpr : BExpr → String
    show-BExpr true = "true"
    show-BExpr false = "false"
    show-BExpr (not b) = "not " Data.String.++ show-BExpr b
    show-BExpr (b and b₁) = show-BExpr b Data.String.++ " and " Data.String.++ show-BExpr b₁
    show-BExpr (b or b₁) = show-BExpr b Data.String.++ " or " Data.String.++ show-BExpr b₁
    show-BExpr (x gt x₁) = show-AExpr x Data.String.++ " gt " Data.String.++ show-AExpr x₁

    show-Stmt : Stmt → String
    show-Stmt ((v := e) l) = show-Var v Data.String.++ " := " Data.String.++ show-AExpr e 
    show-Stmt (skip l) = "skip"
    show-Stmt (s seq s₁) = show-Stmt s Data.String.++ " seq\n" Data.String.++ show-Stmt s₁
    show-Stmt (if (x , _) then s else s₁) = "if " Data.String.++ show-BExpr x Data.String.++ " then " Data.String.++ show-Stmt s Data.String.++ " else " Data.String.++ show-Stmt s₁
    show-Stmt (while (x , _) do s) = "while " Data.String.++ show-BExpr x Data.String.++ " do " Data.String.++ show-Stmt s
    show-Stmt (call c name r args result) = "call " Data.String.++ show-Fun name Data.String.++ " ⟨ " Data.String.++ Data.List.foldr Data.String._++_ "" (Data.List.map show-AExpr args) Data.String.++ show-Var result Data.String.++ " ⟩ "

    init⋆ : Program → Lab
    init⋆ begin declarations main-is main end = init main

    final⋆ : Program → List Lab
    final⋆ begin declarations main-is main end = final main

{-
    blocks⋆ : Program → List Block -- must be done with AG,
-}

    flow⋆ : Program → List Edge
    flow⋆ p@(begin declarations main-is main end) = (concat ∘ Data.List.map (λ{ (proc name ⟨ arguments , result ⟩ n is body end x) → (n , init body) ∷ Data.List.map (λ x₁ → n , x₁) (final body) Data.List.++ flow body })) declarations Data.List.++ flow main

{-
    inter-flow-Stmt : Stmt → List (Lab × Lab × Lab × Lab)
    inter-flow-Stmt ((v := e) l) = []
    inter-flow-Stmt (skip l) = []
    inter-flow-Stmt (s seq s₁) = inter-flow-Stmt s Data.List.++ inter-flow-Stmt s₁
    inter-flow-Stmt (if x then s else s₁) = inter-flow-Stmt s Data.List.++ inter-flow-Stmt s₁
    inter-flow-Stmt (while x do s) = inter-flow-Stmt s
    inter-flow-Stmt (call c n r a r₁) = f (Data.Vec.lookup n functions) 
     where
      f : Decl →  List (Lab × Lab × Lab × Lab)
      f (proc name ⟨ arguments , result ⟩ entry is body end exit) = (c , entry , exit , r) ∷ []

    inter-flow-Decl : Decl → List (Lab × Lab × Lab × Lab)
    inter-flow-Decl (proc name ⟨ arguments , result ⟩ entry is body end exit) = inter-flow-Stmt body

    inter-flow : List (Lab × Lab × Lab × Lab)
    inter-flow = inter-flow' labelledProgram
     where
      inter-flow' : Program → List (Lab × Lab × Lab × Lab)
      inter-flow' begin declarations main-is main end = foldr (λ decl → Data.List._++_ (inter-flow-Decl decl)) (inter-flow-Stmt main) declarations



    flowᴿ : Stmt → List Edge
    flowᴿ s = {!!}



    identifier voor labels zodat we de juiste type functies op de juiste plekken hebben
    dwz.  overal unaire functies, behalve op plekken waar een return label is, daar verwachte we een binaire transfer functie.

    dan om de flow te bepalen,
    edges bestaan normaal uit a → b,  waar a het beginpunt en b het doel.
    maar nu gaan we een binaire edge toevoegen, namelijk een edge zodanig dat:   a,b → c  waar a en b beginpunten en c het doel.
    informatie flowed nu vanuit willekeurige calls naar de entry, die gaat naar exit en vervolgens met de informatie voor de call terug naar ALLE returns.

    nu gaan we de juiste informatie onderscheiden door het gebruik van context
    in dit geval call strings
    zodat we enkel de informatie gebruiken die voor deze return geldt.

    het nadeel dat we nu tegenkomen is dat we niet voldoende informatie hebben? (is dat wel zo?) om de flow om te draaien.

    a → b → c → d \
    a           →  e
    =>
    e → d → c → b \
    e           →  a

    a → b → c → d \
    a → f →  e
    =>
    e → d → c → b \
    e           →  a
-}
