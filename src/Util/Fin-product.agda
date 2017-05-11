module Fin-product where

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ n + m = Succ (n + m)

_*_ : Nat -> Nat -> Nat
Zero * m = Zero
Succ n * m = m + (n * m)

data Fin : Nat -> Set where
  Fz : {n : Nat} -> Fin (Succ n)
  Fs : {n : Nat} -> Fin n -> Fin (Succ n)  

finl : forall {m} -> (n : Nat) -> Fin m -> Fin (m + n)
finl n Fz = Fz
finl n (Fs i) = Fs (finl n i)

finr : forall {n} -> (m : Nat) -> Fin n -> Fin (m + n)
finr Zero i = i
finr (Succ m) i = Fs (finr m i)

data FinPlus (m n : Nat) : Fin (m + n) -> Set where
  IsFinl : (i : Fin m) -> FinPlus m n (finl n i)
  IsFinr : (i : Fin n) -> FinPlus m n (finr m i)

finPlus : (m n : Nat) -> (i : Fin (m + n)) -> FinPlus m n i
finPlus Zero n i = IsFinr i
finPlus (Succ m) n Fz = IsFinl Fz
finPlus (Succ m) n (Fs i) with finPlus m n i
finPlus (Succ m) n (Fs .(finl n i)) | IsFinl i = IsFinl (Fs i)
finPlus (Succ m) n (Fs .(finr m i)) | IsFinr i = IsFinr i















fpair : {m n : Nat} -> Fin m -> Fin n -> Fin (m * n)
fpair {_} {n} Fz j = finl _ j
fpair {n = n} (Fs {k} i) j = finr n (fpair i j)

data FTimes {m n : Nat} : Fin (m * n) -> Set where
  IsFPair : (i : Fin m) -> (j : Fin n) -> FTimes (fpair i j)

finTimes : (m n : Nat) -> (i : Fin (m * n)) -> FTimes {m} {n} i
finTimes Zero n ()
finTimes (Succ m) n i with finPlus n (m * n) i
finTimes (Succ m) n .(finl (m * n) i) | IsFinl i = IsFPair Fz i
finTimes (Succ m) n .(finr n i) | IsFinr i with finTimes m n i
finTimes (Succ m) n .(finr n (fpair i j))
  | IsFinr .(fpair i j) | IsFPair i j = IsFPair (Fs i) j


data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

foo : ∀ {m n} -> Fin (m * n) -> Pair (Fin m) (Fin n)
foo {m} {n}  i with finTimes m n i
foo .(fpair i j) | IsFPair i j = i , j

oof : ∀ {m n} -> Pair (Fin m) (Fin n) -> Fin (m * n)
oof (x , x₁) = fpair x x₁

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x


fsInj : {m : Nat} {i j : Fin m} -> Fs i == Fs j -> i == j
fsInj Refl = Refl

cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

finlInj : (m : Nat) (n : Nat) (i j : Fin n) ->
  finl m i == finl m j -> i == j
finlInj m _ Fz Fz p = Refl
finlInj m _ Fz (Fs j) ()
finlInj m _ (Fs i) Fz ()
finlInj m _ (Fs i) (Fs j) p = cong Fs (finlInj m _ i j (fsInj p))

finrInj : (m : Nat) (n : Nat) (i j : Fin n) ->
  finr m i == finr m j -> i == j
finrInj Zero n i j p = p
finrInj (Succ m) n i j p = finrInj m n i j (fsInj p)

fpairInj1' : {m n : Nat} -> (i i' : Fin n) -> (j : Fin m) ->
  fpair i j == fpair i' j -> i == i'
fpairInj1' {m} {n} i i' j x = {!!}

fpairInj1 : {m n : Nat} -> (i i' : Fin n) -> (j : Fin m) ->
  fpair i j == fpair i' j -> i == i'
fpairInj1 Fz Fz j p = Refl
fpairInj1 {m} {n} (Fz {m₁}) (Fs {n₂} i') j p with fpair i' j
fpairInj1 {m} {.(Succ Zero)} (Fz {Zero}) (Fs {.Zero} i') j p | ()
fpairInj1 {Zero} {.(Succ (Succ n))} (Fz {Succ n}) (Fs {.(Succ n)} i') () p | q
fpairInj1 {Succ m} {.(Succ (Succ n))} (Fz {Succ n}) (Fs {.(Succ n)} i') j p | Fz = {!p!}
fpairInj1 {Succ m} {.(Succ (Succ n))} (Fz {Succ n}) (Fs {.(Succ n)} i') j p | Fs q = {!!}
fpairInj1 (Fs i) Fz j p = {!p!}
fpairInj1 {m} (Fs {n} i) (Fs {.n} i') j p = cong Fs
  (fpairInj1 i i' j (finrInj m (n * m) (fpair i j) (fpair i' j) p))



fpairInj2 : {m n : Nat} -> (i : Fin n) -> (j j' : Fin m) ->
  fpair i j == fpair i j' -> j == j'
fpairInj2 Fz j j' p = finlInj _ _ j j' p
fpairInj2 {m} (Fs {n} i) j j' p =
  fpairInj2 i j j' (finrInj m (n * m) (fpair i j) (fpair i j') p)


fooCorrect : ∀ {m n} -> (x : Fin (m * n))
  -> (i : Fin n) -> (j : Fin m) ->
  x == fpair j i ->
  foo x == (j , i)
fooCorrect {m} {n} x i j p with finTimes m n x
fooCorrect {m} {n} .(fpair i j) i₁ j₁ p | IsFPair i j = {!fpairInj1 {?} {m} i j₁ j!}

{- with fpairInj1 {n} {m} {!!} {!fp!} {!i₁!} p
... | q = {!fpairInj1 {n} {m} ? ? ? p!} -}

id1 : ∀ {m n} -> (p : Pair (Fin m) (Fin n)) -> foo (oof p) == p
id1 {m} {n} (x , x₁) = fooCorrect (fpair x x₁) x₁ x Refl

id2 : ∀ {m n} -> (i : (Fin (m * n))) -> oof {m} {n} (foo i) == i
id2 {m} {n} i with finTimes m n i
id2 .(fpair i j) | IsFPair i j = Refl
