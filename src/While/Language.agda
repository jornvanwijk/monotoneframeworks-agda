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

module While.Language where
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

    
    record Stmt-Algebra (A : Set) (B : Set) (C : Set) : Set where
      field
        bExprAlg : BExpr-Algebra String A B
        _:=*_ : (v : String) → (e : A) → C
        skip* : C
        _seq*_ : (l : C) → (r : C) → C
        if*_then_else_ : (c : B) → (t : C) → (f : C) → C
        while*_do_ : (c : B) → (b : C) → C
    
    foldStmt : {A B C : Set} → Stmt-Algebra A B C → Stmt → C
    foldStmt {A} {B} {C} record { bExprAlg = bExprAlg ; _:=*_ = _:=*_ ; skip* = skip* ; _seq*_ = _seq*_ ; if*_then_else_ = if*_then_else_ ; while*_do_ = while*_do_ } e = f e
     where f : Stmt → C
           f (v := e₁) = v :=* foldAExpr (BExpr-Algebra.aExprAlg bExprAlg) e₁
           f skip = skip*
           f (s seq s₁) = f s seq* f s₁
           f (if c then s else s₁) = if* foldBExpr bExprAlg c then f s else f s₁
           f (while c do s) = while* foldBExpr bExprAlg c do f s
  

  module Labeled where
    
    open Common hiding (AExpr ; BExpr) public
    open Unlabeled hiding (AExpr ; BExpr ; Stmt)
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
  
    data Stmt' {a} {b} (Lab : Set a) (Var : Set b) : Set (a Level.⊔ b) where
      _:=_ : (v : Var) → (e : Common.AExpr Var) → (l : Lab) → Stmt' Lab Var
      skip : (l : Lab) → Stmt' Lab Var
      _seq_ : (s₁ : Stmt' Lab Var) → (s₂ : Stmt' Lab Var) → Stmt' Lab Var
      if_then_else_ : (Common.BExpr Var × Lab) → (t : Stmt' Lab Var) → (f : Stmt' Lab Var) → Stmt' Lab Var
      while_do_ : (Common.BExpr Var × Lab) → (b : Stmt' Lab Var) → Stmt' Lab Var

    data Block' {a} {b} (Lab : Set a) (Var : Set b) : Set (a Level.⊔ b) where
      skip : (l : Lab) → Block' Lab Var
      _:=_ : (x : Var) → (a : Common.AExpr Var) → (l : Lab) → Block' Lab Var
      bExpr : (c : Common.BExpr Var) → (l : Lab) → Block' Lab Var

    record WhileProgram : Set₁ where
      field
        n : ℕ
        Var* : Bag String
      m : ℕ
      m = length (Util.Bag.toList Var*)
      Lab : Set
      Lab = Fin n
      Var : Set
      Var = Fin m
      AExpr : Set
      AExpr = Common.AExpr Var
      BExpr : Set
      BExpr = Common.BExpr Var
      Stmt : Set
      Stmt = Stmt' Lab Var
      Block : Set
      Block = Block' Lab Var
      field
        blocks : Vec Block n
        labelledProgram : Stmt



  module Generated (program : Unlabeled.Stmt) where
    open Labeled
    
    open Common hiding (AExpr ; BExpr) public
    open Unlabeled hiding (AExpr ; BExpr ; Stmt)
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
    --
    example' : Stmt-Algebra
                 ((prevV : Bag String) → Σ[ curV ∈ Bag String ] ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.AExpr (Fin (length (Util.Bag.toList allVariables)))))
                 ((prevV : Bag String) → Σ[ curV ∈ Bag String ] ((allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables × Common.BExpr (Fin (length (Util.Bag.toList allVariables)))))
                 ((prevL : ℕ) → (prevV : Bag String) → Σ[ curL ∈ ℕ ] Σ[ curV ∈ Bag String ] ((maxL : ℕ) → curL Data.Nat.≤ maxL → (allVariables : Bag String) → Util.Bag.toList curV ⊆ Util.Bag.toList allVariables → Σ[ pL ∈ (prevL Data.Nat.≤ maxL) ] Σ[ pV ∈ (Util.Bag.toList prevV ⊆ Util.Bag.toList allVariables) ] Σ[ t ∈ Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))]
                 ((prevBlock : Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) prevL) → Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) curL)))
    var* (aExprAlg (bExprAlg example')) x (xs , nodup) with x ∈?[ Data.String._≟_ ] xs
    var* (aExprAlg (bExprAlg example')) x (xs , nodup) | yes p = (xs , nodup) , (λ allVariables₁ x₁ → x₁ , (var (index (x₁ p))))
    var* (aExprAlg (bExprAlg example')) x (xs , nodup) | no ¬p = ((x ∷ xs) , (¬p ::: nodup)) , (λ allVariables₁ x₁ → (λ x₃ → x₁ (there x₃)) , var (index (x₁ (here refl)))) 
    lit* (aExprAlg (bExprAlg example')) z prevV = prevV , (λ allVariables₁ x → x , lit z)
    _plus*_ (aExprAlg (bExprAlg example')) x y prevV = let (a , b) = x prevV
                                                           (c , d) = y a
                                                       in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                                       (m , n) = b allVariables k
                                                                                   in m , (n plus l))
    _min*_ (aExprAlg (bExprAlg example')) x y prevV = let (a , b) = x prevV
                                                          (c , d) = y a
                                                      in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                                      (m , n) = b allVariables k
                                                                                  in m , (n min l))
    _mul*_ (aExprAlg (bExprAlg example')) x y prevV = let (a , b) = x prevV
                                                          (c , d) = y a
                                                      in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                                      (m , n) = b allVariables k
                                                                                  in m , (n mul l))
    true* (bExprAlg example') prevV = prevV , (λ allVariables₁ x → x , true)
    false* (bExprAlg example') prevV = prevV , (λ allVariables₁ x → x , false)
    not* (bExprAlg example') x prevV = let (a , b) = x prevV
                                       in a , (λ allVariables₁ x₁ → let (c , d) = b allVariables₁ x₁
                                                                    in c , not d) 
    _and*_ (bExprAlg example') x y prevV = let (a , b) = x prevV
                                               (c , d) = y a
                                           in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                           (m , n) = b allVariables k
                                                                       in m , (_and_ n l))
    _or*_ (bExprAlg example') x y prevV = let (a , b) = x prevV
                                              (c , d) = y a
                                          in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                          (m , n) = b allVariables k
                                                                      in m , (_or_ n l))
    _gt*_ (bExprAlg example') x y prevV = let (a , b) = x prevV
                                              (c , d) = y a
                                          in c , (λ allVariables x₁ → let (k , l) = d allVariables x₁
                                                                          (m , n) = b allVariables k
                                                                      in m , (_gt_ n l))
    _:=*_ example' x y prevL (xs , nodup) with x ∈?[ Data.String._≟_ ] xs
    _:=*_ example' x y prevL (xs , nodup) | yes p = let (yV , yF) = y (xs , nodup)
                                                    in (ℕ.suc prevL) , (yV , (λ maxL x₁ allVariables₁ x₂ → let (yPV , yT) = yF allVariables₁ x₂ 
                                                                                                            in (decrement-left x₁) , yPV , (index (yPV p) := yT) (fromℕ≤ x₁) , (λ prevBlock → prevBlock 𝕍.∷ʳ (index (yPV p) := yT) (fromℕ≤ x₁) ) {- _∷_ ((index (yPV p) := yT) (fromℕ≤ x₁)) -} ))
    _:=*_ example' x y prevL (xs , nodup) | no ¬p = let (yV , yF) = y (x ∷ xs , ¬p ::: nodup)
                                                    in (ℕ.suc prevL) , (yV , (λ maxL x₁ allVariables₁ x₂ → let (yPV , yT) = yF allVariables₁ x₂
                                                                                                            in decrement-left x₁ , (λ x₄ → yPV (there x₄)) , ((index (yPV (here refl)) := yT) (fromℕ≤ x₁) , (𝕍._∷ʳ (index (yPV (here refl)) := yT) (fromℕ≤ x₁)) {- _∷_ ((index (yPV (here refl)) := yT) (fromℕ≤ x₁)) -} )))
    skip* example' prevL prevV = ℕ.suc prevL , (prevV , (λ maxL x allVariables₁ x₁ → decrement-left x , (x₁ , skip (fromℕ≤ x) , 𝕍._∷ʳ (skip (fromℕ≤ x)))))
    _seq*_ example' x y prevL prevV = let (xL , xV , xF) = x prevL prevV
                                          (yL , yV , yF) = y xL xV
                                      in yL , (yV , (λ maxL x₁ allVariables₁ x₂ → let (yPL , yPV , yT , yG) = yF maxL x₁ allVariables₁ x₂ 
                                                                                      (xPL , xPV , xT , xG) = xF maxL yPL allVariables₁ yPV
                                                                                  in xPL , (xPV , (xT seq yT) , (λ prevBlock → let xB = xG prevBlock
                                                                                                                                   yB = yG xB
                                                                                                                               in yB))))
    if*_then_else_ example' b t f prevL prevV = let (bV , bF) = b prevV
                                                    (tL , tV , tF) = t (ℕ.suc prevL) bV
                                                    (fL , fV , fF) = f tL tV
                                                in fL , (fV , (λ maxL x allVariables₁ x₁ → let (fPL , fPV , fT , fG) = fF maxL x allVariables₁ x₁ 
                                                                                               (tPL , tPV , tT , tG) = tF maxL fPL allVariables₁ fPV 
                                                                                               (bPV , bT) = bF allVariables₁ tPV 
                                                                                           in decrement-left tPL , (bPV , (if (bT , fromℕ≤ tPL) then tT else fT) , (λ prevBlock →
                                                                                                  let tB = tG (prevBlock 𝕍.∷ʳ bExpr bT (fromℕ≤ tPL)) --(prevBlock 𝕍.∷ᵗ ())
                                                                                                      fB = fG tB
                                                                                                  in fB))))
    while*_do_ example' c b prevL prevV = let (cV , cF) = c prevV
                                              (bL , bV , bF) = b (ℕ.suc prevL) cV
                                          in bL , (bV , (λ maxL x allVariables₁ x₁ → let (bPL , bPV , bT , bG) = bF maxL x allVariables₁ x₁ 
                                                                                         (cPV , cT) = cF allVariables₁ bPV
                                                                                     in (decrement-left bPL) , (cPV , (while (cT , fromℕ≤ bPL) do bT),
                                                                                       (λ prevBlock → bG (prevBlock 𝕍.∷ʳ bExpr cT (fromℕ≤ bPL))) {- (𝕍._∷ʳ (bG (bExpr cT (fromℕ≤ bPL)))) -})))
                                                                                     

    re : Σ[ maxL ∈ ℕ ] Σ[ allVariables ∈ Bag String ] Stmt' (Fin maxL) (Fin (length (Util.Bag.toList allVariables))) × Vec (Block' (Fin maxL) (Fin (length (Util.Bag.toList allVariables)))) maxL
    re = let (maxL , allVariables , f) = foldStmt example' program 0 ([] , end)
         in maxL , (allVariables , (let (pL , pV , pT , pG) = f maxL (≤′⇒≤ ≤′-refl) allVariables Function.id
                                    in pT , (pG Vec.[])))

    whileProgram : WhileProgram
    whileProgram = record
                     { n = proj₁ re
                     ; Var* = proj₁ (proj₂ re)
                     ; blocks = proj₂ (proj₂ (proj₂ re))
                     ; labelledProgram =  proj₁ (proj₂ (proj₂ re))
                     }


  module Extra (open Labeled) (p : WhileProgram) where
    open WhileProgram p
    open Unlabeled hiding (AExpr ; BExpr ; Stmt)
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
    
    init : Stmt → Lab
    init ((v := e) l) = l
    init (skip x) = x
    init (s seq s₁) = init s
    init (if proj₁ , proj₂ then s else s₁) = proj₂
    init (while proj₁ , proj₂ do s) = proj₂

    final : Stmt → List Lab
    final ((v := e) l) = Data.List.[ l ]
    final (skip l) = Data.List.[ l ]
    final (s seq s₁) = final s₁
    final (if proj₁ , proj₂ then s else s₁) = final s Data.List.++ final s₁
    final (while proj₁ , proj₂ do s) = Data.List.[ proj₂ ]

    labels : Stmt → List Lab
    labels ((v := e) l) = Data.List.[ l ]
    labels (skip l) = Data.List.[ l ]
    labels (s seq s₁) = labels s Data.List.++ labels s₁
    labels (if x then s else s₁) = proj₂ x ∷ labels s Data.List.++ labels s₁
    labels (while x do s) = proj₂ x ∷ labels s
  
    flow : Stmt → List (Lab × Lab)
    flow ((v := e) l) = []
    flow (skip l) = []
    flow (s seq s₁) = flow s ++ flow s₁ ++ Data.List.map (λ x → x , init s₁) (final s)
    flow (if x then s else s₁) = ((proj₂ x) , (init s)) ∷ ((proj₂ x) , (init s₁)) ∷ flow s ++ flow s₁
    flow (while x do s) = ((proj₂ x) , (init s)) ∷ flow s ++ Data.List.map (λ l' → l' , proj₂ x) (final s)

    open import Data.Graph n
    
    flowᴿ : Stmt → List (Lab × Lab)
    flowᴿ s = flow s ᴿ

    open import Data.String
    show-Var : Var → String
    show-Var v = Data.Vec.lookup v (Data.Vec.fromList (proj₁ Var*))
    
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

