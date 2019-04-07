
module Sheeps

import Data.Vect
import Data.Vect.Quantifiers

%default total

data SlotState = B | F | E

data Token : SlotState -> Type where
  Forward : Token F
  Backward : Token B

record EmptySlot (s : SlotState) where
  constructor MkEmptySlot
  slot : EmptySlot E

Forw : Type
Forw = Token F

Bacw : Type
Bacw = Token B

Eq SlotState where
  B == B = True
  F == F = True
  E == E = True
  _ == _ = False

DecEq SlotState where
  decEq B B = Yes Refl
  decEq F F = Yes Refl
  decEq E E = Yes Refl
  decEq _ _ = No believe_me

record InitialConfig (l : Nat) (r : Nat) where
  constructor MkInitialConfig
  initial : Vect x f -> Vect y b -> {auto eqf : f = Forw} -> {auto eqb : b = Bacw} -> InitialConfig x y

Solvable : Nat -> Nat -> Type
Solvable a b = InitialConfig a b = InitialConfig b a

-- Vect n Bool encodes a vector of either forward or backward tokens by erasing the token type

StateToType : SlotState -> Type
StateToType B = Token B
StateToType F = Token F
StateToType E = EmptySlot E

toVectToken : Vect n SlotState -> Vect n Type
toVectToken = map StateToType

dropLast : Vect (S n) a -> Vect n a
dropLast (x :: []) = []
dropLast (x :: (y :: xs)) = x :: (dropLast (y :: xs))

dropFirst : Vect (S n) a -> Vect n a
dropFirst = tail

canMoveOneLeft : {n : Nat} -> Fin n -> Vect (S n) SlotState -> Bool
canMoveOneLeft x xs = let slot = index x (dropLast xs) in slot == E

canMoveTwoLeft : Fin n -> Vect (S n) SlotState -> Bool

moveOneLeftNotStuck : Fin n -> Vect (S n) SlotState -> Bool


moveTwoNotStuck : Fin n -> Vect (S n) SlotState -> Bool

||| Given a vector of size (S n), check if the and a (Fin n), check if the (n+1)th token can be moved left
||| The token can be moved IFF the left position is free, or the left position is taken by an opposite token
||| but the second left position is free, and moving does not create a stuck state
canMoveLeft : {n : Nat} -> Fin n -> Vect (S n) SlotState -> Bool
canMoveLeft x xs = canMoveOneLeft x xs && moveOneLeftNotStuck x xs || canMoveTwoLeft x xs && moveTwoNotStuck x xs


data InVect : (elem : a) -> (index : Fin n) -> (vec : Vect n a) -> Type where
  Here :  InVect e FZ (e :: xs)
  There : InVect e i xs -> InVect e (FS i) (x :: xs)

Th : (v1 : InVect e i xs) -> InVect e (FS i) (x :: xs)
Th = There

getIndex : {e : a} -> {v : Vect n a} -> InVect e i v -> Fin n
getIndex v {i} = i

getIndexProof : (index : InVect e i v) -> getIndex index = i
getIndexProof index = Refl

Uninhabited (InVect e i []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

ElemNotThere : DecEq a => (e1, e2 : a) -> Type
ElemNotThere e1 e2 = (contra : (e1 = e2 -> Void) ** decEq e1 e2 = No contra)

||| Fix that later, it should be provable that it leads to a contradiction
postulate findInVectNowhere : {elem : a} -> {xs : Vect len a} -> ((i : Fin len ** InVect elem i xs) -> Void) -> (i : Fin (S len) ** InVect elem i (x :: xs)) -> Void

findInVect : (DecEq a) => (elem : a) -> (v : Vect n a) -> Dec (i : Fin n ** InVect elem i v)
findInVect elem [] = No (\(idx ** vect) => absurd vect)
findInVect elem (x :: xs) with (decEq elem x)
  findInVect x (x :: xs) | (Yes Refl) = Yes (FZ ** Here)
  findInVect elem (x :: xs) | (No contra) with (findInVect elem xs)
    findInVect elem (x :: xs) | (No contra) | (Yes (idx ** vec)) = Yes (FS idx ** There vec)
    findInVect elem (x :: xs) | (No contra) | (No f) = No (findInVectNowhere f)

infixl 3 ^

(^) : (a -> a) -> Nat -> a -> a
f ^ Z = id
f ^ (S n) = f . (f ^ n)

w : Fin n -> Fin (S n)
w = weaken

||| There are only 4 legal moves: 
||| […, F, E, …], F can move forward once -> […, E, F, …]
||| […, F, B, E, …] F can move forward by jumping -> […, E, B, F, …]
||| […, E, B, …], B can move backward once -> […, B, E, …]
||| […, E, F, B, …], B can move backward by jumping -> […, B, F, E, …]
data Move : Vect n SlotState -> Type where
  NextLeft  : InVect E (    w idx) xs -> InVect B (    FS idx) xs                              -> Move xs
  JumpLeft  : InVect E (w $ w idx) xs -> InVect F (w $ FS idx) xs -> InVect B (FS $ FS idx) xs -> Move xs
  NextRight : InVect F (    w idx) xs -> InVect E (    FS idx) xs                              -> Move xs
  JumpRight : InVect F (w $ w idx) xs -> InVect B (w $ FS idx) xs -> InVect E (FS $ FS idx) xs -> Move xs

getVect : {xs : Vect n SlotState} -> Move xs -> Vect n SlotState
getVect x {xs} = xs

proveVectMove : (move : Move xs) -> xs = getVect move
proveVectMove move = Refl

swapPositions : {a, b : e} -> (i, j : Fin n) -> (vec : Vect n e) -> {auto present1 : InVect a i vec} -> {auto present2 : InVect b j vec} -> Vect n e
swapPositions i j vec {a} {b} = updateAt j (const a) $ updateAt i (const b) vec

StillThere : InVect a i vec -> InVect b j vec -> Type
StillThere x y {a} {b} {i} {j} {vec} = let swapped = swapPositions i j vec in (InVect b i swapped, InVect a j swapped)

proofSwap : (vec : Vect n e) -> (first : InVect a i vec) -> (second : InVect b j vec)  -> StillThere first second
proofSwap (a :: xs) Here Here = (Here,Here)
proofSwap (a :: xs) Here (There x) = (Here, ?proofSwap1)
proofSwap (x :: xs) (There y) Here = (?proofSwap_rhs2, Here)
proofSwap (x :: xs) (There y) (There z) = (?proofSwap_rhs1, ?proofSwap_rhs2)

performMove : (vec : Vect n SlotState) -> Move vec -> Vect n SlotState
performMove vec (NextLeft e b) = swapPositions (getIndex b) (getIndex e) vec
performMove vec (JumpLeft e f b) = swapPositions (getIndex b) (getIndex e) vec
performMove vec (NextRight f e) = swapPositions (getIndex f) (getIndex e) vec
performMove vec (JumpRight f b e) = swapPositions (getIndex f) (getIndex e) vec

IsBack : SlotState -> Type
IsBack s = s = B

IsForw : SlotState -> Type
IsForw s = s = F

IsEmpty : SlotState -> Type
IsEmpty s = s = F

OnlyForward : Vect n SlotState -> Type 
OnlyForward vec = All IsForw vec

OnlyBackward : Vect n SlotState -> Type
OnlyBackward vec = All IsBack vec

OnlyEmpty : Vect n SlotState -> Type 
OnlyEmpty vec = All IsEmpty vec

allB : (vec : Vect n SlotState) -> {auto prf : All IsBack vec} -> OnlyBackward vec
allB vec {prf} = prf

allF : (vec : Vect n SlotState) -> {auto prf : All IsForw vec} -> OnlyForward vec
allF vec {prf} = prf

data IsSolved : Vect n SlotState -> Type where
  MkSolved : OnlyBackward left -> OnlyForward right -> IsSolved (left ++ [E] ++ right)

getSolution : {vec : Vect n SlotState} -> IsSolved vec -> Vect n SlotState
getSolution x {vec} = vec

-- 1n•1b solvable:
baseMoveLeft : Move [F, E, B]
baseMoveLeft = NextLeft (There Here) (There (There Here))

thenJumpRight : Move [F, B, E]
thenJumpRight = JumpRight Here (There Here) (There (There Here))

thenMoveLeftLeft : Move [E, B, F]
thenMoveLeftLeft = NextLeft Here (There Here)

firstMove : performMove [F, E, B] Sheeps.baseMoveLeft = [F, B, E]
firstMove = Refl

secondMove : performMove [F, B, E] Sheeps.thenJumpRight = [E, B, F]
secondMove = Refl

thridMove : performMove [E, B, F] Sheeps.thenMoveLeftLeft = [B, E, F]
thridMove = Refl

proveIsSolved : IsSolved [B, E, F]
proveIsSolved = MkSolved (allB [B]) (allF [F])

data IsSolvable : Vect n SlotState -> Type where
  Solved : IsSolved vec -> IsSolvable vec
  Step : (m : Move vec) -> IsSolvable (performMove vec m) -> IsSolvable vec


-- prove1n1b : IsSolvable [F, E, B]
-- prove1n1b = Step baseMoveLeft 
--           $ Step thenJumpRight 
--           $ Step thenMoveLeftLeft 
--           $ Solved proveIsSolved
-- 
-- 
-- prove2n1b : IsSolvable [F, F, E, B]
-- prove2n1b = Step (NextLeft (There (There Here)) (There (There (There Here)))) -- [F, F, B, E]
--           $ Step (JumpRight (There Here) (There (There Here)) (There (There (There Here)))) -- [F, E, B, F]
--           $ Step (NextLeft (There Here) (There (There Here))) -- [F, B, E, F]
--           $ Step (JumpRight (Here) (There Here) (There (There Here))) -- [E, B, F, F]
--           $ Step (NextLeft (Here) (There Here)) -- [B, E, F, F]
--           $ Solved (MkSolved (allB [B]) (allF [F, F]))
-- 
-- prove2n2b : IsSolvable [F, F, E, B, B]                                                  -- [F, F, E, B, B]
-- prove2n2b = Step (NextLeft (Th (Th Here)) (Th (Th (Th Here))))                          -- [F, F, B, E, B]
--           $ Step (JumpRight (Th Here) (Th (Th Here)) (Th (Th (Th Here))))               -- [F, E, B, F, B]
--           $ Step (NextRight (Here) (Th Here))                                           -- [E, F, B, F, B]
--           $ Step (JumpLeft Here (Th Here) (Th (Th Here)))                               -- [B, F, E, F, B]
--           $ Step (JumpLeft (Th (Th Here)) (Th (Th (Th Here))) (Th (Th (Th (Th Here))))) -- [B, F, B, F, E]
--           $ Step (NextRight (Th (Th (Th Here))) (Th (Th (Th (Th Here)))))               -- [B, F, B, E, F]
--           $ Step (JumpRight (Th Here) (Th (Th Here)) (Th (Th (Th Here))))               -- [B, E, B, F, F]
--           $ Step (NextLeft (Th Here) (Th (Th Here)))                                    -- [B, B, E, F, F]
--           $ Solved (MkSolved (allB [B, B]) (allF [F, F]))
-- 

proofConcatEq : {left : OnlyBackward l} -> {right : OnlyForward r} -> (left ++ E :: right) ++ [F] = left ++ (E :: right ++ [F])

RighPaddedSolved : IsSolvable a -> IsSolvable (a ++ [F])
RighPaddedSolved (Solved (MkSolved y z)) = Solved (rewrite cong {f=IsSolved} proofConcatEq in ?RighPaddedSolved_rhs_4)
RighPaddedSolved (Step m x) = ?RighPaddedSolved_rhs_2

-- Some properties of the rules

-- An empty array has no legal moves
Uninhabited (Move []) where
  uninhabited (NextLeft _ _) impossible
  uninhabited (JumpLeft _ _ _) impossible
  uninhabited (NextRight _ _) impossible
  uninhabited (JumpRight _ _ _) impossible

-- You can't find B in [E]
Uninhabited (InVect B (FS idx) [E]) where
  uninhabited (There Here) impossible
  uninhabited (There (There _)) impossible

-- You can't find F in [E]
Uninhabited (InVect F (FS idx) [E]) where
  uninhabited (There Here) impossible
  uninhabited (There (There _)) impossible

-- An empty harray had no legal moves
Uninhabited (Move [E]) where
  uninhabited (NextLeft x y) = absurd y
  uninhabited (NextRight (There Here) _) impossible
  uninhabited (NextRight (There (There _)) _) impossible




-- 
-- JumpLeft
-- given Vect 10 JUmp Left "i" has to  and jumpLeftTarget has to be t with max size Fin (S (S t))
