module ULC

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Decidable.Equality
import Proofs

%default total

-- Variable ih stands for Inductive Hypothesis.

-- Variables are strings for convenience.
V : Type
V = String

-- Lists are Multisets to help mathematicians (but not really).
Multiset : Type -> Type
Multiset = List

||| Definition of untyped λ calculus.
|||  (1) (Variable) if u∈V, then u∈Λ. 
|||  (2) (Application) if M∈Λ and N∈Λ then (M N)∈Λ.
|||  (3) (Abstraction) if u∈V and M∈Λ, then (λu.M)∈Λ.
data Λ : Type where
 Var : V -> Λ
 App : Λ -> Λ -> Λ
 Abs : V -> Λ -> Λ

||| Proof that ∀x, y, z. Var(x) ≡ App(y, z) ⇒ ⊥.
Uninhabited (Var x = App y z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. App(x, y) ≡ Var(z) ⇒ ⊥.
Uninhabited (App x y = Var z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Var(x) ≡ Abs(y, z) ⇒ ⊥.
Uninhabited (Var x = Abs y z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Abs(x, y) ≡ Var(z) ⇒ ⊥.
Uninhabited (Abs x y = Var z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. App(x, y) ≡ Abs(z, w) ⇒ ⊥.
Uninhabited (App x y = Abs z w) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Abs(x, y) ≡ App(z, w) ⇒ ⊥.
Uninhabited (Abs x y = App z w) where
  uninhabited Refl impossible

||| Proof that App(x, y) ≡ App(q, r) -> x ≡ q ∧ y ≡ r.
appElemjective : (0 prf : App x y = App q r) -> (x = q, y = r)
appElemjective Refl = (Refl, Refl)

||| Proof that Abs(x, y) ≡ Abs(q, r) -> x ≡ q ∧ y ≡ r.
absElemjective : (0 prf : Abs x y = Abs q r) -> (x = q, y = r)
absElemjective Refl = (Refl, Refl)

-- pretty printing for untyped λ calculus.
implementation Show Λ where
  show (Var x)   = x
  show (App m n) = "" ++ show m ++ " " ++ show n ++ ""
  show (Abs x m) = "λ" ++ x ++ "." ++ show m ++ ""

implementation Eq Λ where
  (Var x)   == (Var y)   = x == y
  (Var _)   == (App _ _) = False
  (Var _)   == (Abs _ _) = False
  (App _ _) == (Var _)   = False
  (App x y) == (App z w) = x == z && y == w 
  (App _ _) == (Abs _ _) = False
  (Abs _ _) == (Var _)   = False
  (Abs _ _) == (App _ _) = False
  (Abs x y) == (Abs z w) = x == z && y == w
  x /= y                 = not (x == y)

||| Multiset of subterms of Λ.
|||  Let V denote a set of symbols.
|||  (1) (Variable) sub(x) = {x}, for each x∈V.
|||  (2) (Application) sub((M N)) = sub(M) ⋃ sub(N) ⋃ {(M N)}.
|||  (3) (Abstraction) sub((λx.M)) = sub(M) ⋃ {(λx.M)}.
sub : (1 x : Λ) -> Multiset Λ
sub (Var x) = [Var x]
sub (App m n) = [App m n] ++ sub m ++ sub n
sub (Abs x m) = [Abs x m] ++ sub m

||| Reflexivity Lemma. ∀x∈Λ. x∈sub(x).
reflSubλ : (1 x : Λ) -> Elem x (sub x)
reflSubλ (Var x) = Here
reflSubλ (App x y) = Here
reflSubλ (Abs x y) = Here

||| Proof that ∀z. App(x, y)∈sub(z) ⇒ x∈sub(z).
appLeftArg : (x, z : Λ) -> (1 prf : Elem (App x y) (sub z)) -> Elem x (sub z)
appLeftArg x (Var z) (There p) = absurd p
appLeftArg x (App x y) Here = 
  let prf : Elem x (sub x)
      prf = reflSubλ x
  in There $ elemAppLeft (sub y) prf
appLeftArg x (App z w) (There p) =
 case elemAppLorR (sub z) (sub w) p of
   (Left l)  => 
     let ih : Elem x (sub z)
         ih = appLeftArg x z l 
     in There $ elemAppLeft (sub w) ih
   (Right r) => 
     let ih : Elem x (sub w)
         ih = appLeftArg x w r 
     in There $ elemAppRight (sub z) ih
appLeftArg x (Abs z w) (There p) = There $ appLeftArg x w p

||| Proof that ∀z. App(x, y)∈sub(z) ⇒ y∈sub(z).
appRightArg : (y, z : Λ) -> (1 prf : Elem (App x y) (sub z)) -> Elem y (sub z)
appRightArg y (Var x) (There prf) = absurd prf
appRightArg y (App x y) Here = 
  let prf : Elem y (sub y)
      prf = reflSubλ y
  in There $ elemAppRight (sub x) prf
appRightArg y (App x z) (There p) = 
  case elemAppLorR (sub x) (sub z) p of
    (Left l) => 
      let rec : Elem y (sub x)
          rec = appRightArg y x l 
      in There $ elemAppLeft (sub z) rec
    (Right r) => 
      let rec : Elem y (sub z)
          rec = appRightArg y z r
      in There $ elemAppRight (sub x) rec
appRightArg y (Abs x z) (There p) = There $ appRightArg y z p

||| Proof that ∀z. Abs(x, y)∈sub(z) ⇒ y∈sub(z).
absRightArg : (y, z : Λ) -> (1 prf : Elem (Abs x y) (sub z)) -> Elem y (sub z)
absRightArg y (Var z) (There prf) = absurd prf
absRightArg y (App z w) (There prf) =
  case elemAppLorR (sub z) (sub w) prf of
    (Left l) => 
      let ih : Elem y (sub z)
          ih = absRightArg y z l
      in There $ elemAppLeft (sub w) ih
    (Right r) => 
      let ih : Elem y (sub w)
          ih = absRightArg y w r
      in There $ elemAppRight (sub z) ih
absRightArg y (Abs x y) Here = There $ reflSubλ y
absRightArg y (Abs z w) (There prf) = There $ absRightArg y w prf

||| Transitivity Lemma. x∈sub(y) ∧ y∈sub(z) ⇒ x∈sub(z).
transSubλ : (x, y, z : Λ) -> (prf1: Elem x (sub y)) -> 
            (prf2 : Elem y (sub z)) -> Elem x (sub z)
transSubλ (Var _) (Var _) _ Here prf2 = prf2
transSubλ _ (Var _) _ (There prf) _ = absurd prf
transSubλ (App _ _) (App _ _) _ Here prf2 = prf2
transSubλ x (App y w) z (There prf) prf2 = 
  case elemAppLorR (sub y) (sub w) prf of
    (Left l)  =>
      let prf3 : Elem y (sub z)
          prf3 = appLeftArg y z prf2
      in transSubλ x y z l prf3
    (Right r) =>
      let prf3 : Elem w (sub z)
          prf3 = appRightArg w z prf2
      in transSubλ x w z r prf3
transSubλ (Abs _ _) (Abs _ _) _ Here prf2 = prf2
transSubλ x (Abs y w) z (There prf) prf2 = 
  let prf3 : Elem w (sub z)
      prf3 = absRightArg w z prf2
  in transSubλ x w z prf prf3

||| Multiset of proper sub-terms for Λ.
||| (1) (Variable)    propSub(x) ≡ Ø ∀x∈V.
||| (2) (Application) propSub(App(x, y)) ≡ propSub(x) ⋃ propSub(y) ∧
|||                   propSub(x) ≠ App(x, y) ∧ propSub(y) ≠ App(x, y).
||| (3) (Abstraction) propSub(Abs(x, y)) ≡ propSub(y) ∧ propSub(y) ≠ Abs(x, y).
propSubλ : (1 x : Λ) -> List Λ
propSubλ (Var x) = []
propSubλ (App x y) = 
  case x == (App x y) of
    True => 
      case y == (App x y) of
        True => []
        False => [y] ++ propSubλ y
    False =>
      case y == (App x y) of
        True  => [x] ++ propSubλ x
        False => [x, y] ++ propSubλ x ++ propSubλ y
propSubλ (Abs x y) =
  case y == (Abs x y) of
    True  => [Var x]
    False => [Var x] ++ [y] ++ propSubλ y


||| remove all occurances of x∈X.
remove : (Eq a) => a -> List a -> List a
remove x [] = []
remove x (y :: xs) = if x == y then remove x xs else y :: remove x xs

||| Free variables in Λ.
||| (1) (Variable) if x∈V then fv(x) ≡ {x}.
||| (2) (Application) fv(App(x, y)) ≡ fv(x) ⋃ fv(y).
||| (3) (Application) fv(Abs(x, y)) ≡ fv(y) \ {x}.
fv : (1 x : Λ) -> List V
fv (Var x) = [x]  
fv (App x y) = fv x ++ fv y
fv (Abs x y) = remove x (fv y)

Closed : Λ -> Type
Closed x = fv x = [] 

testPropSub : Λ
testPropSub = App (Var "y") (Abs "x" (App (Var "x") (Var "z")))

testFreeVar : Λ
testFreeVar = Abs "x" (App (Var "x") (Var "y"))

testFreeVar2 : Λ
testFreeVar2 = App (Var "x") (Abs "x" (Var "y"))

testClosed : Λ
testClosed = Abs "x" (Abs "y" (Abs "z" (App (Var "x") 
  (App (Var "x") (Var "y")))))

testClosed2 : Λ
testClosed2 = Abs "x" (Abs "y" (App (Var "x") (App (Var "x") (Var "y"))))

prfClosed : Closed ULC.testClosed
prfClosed = Refl

prfClosed2 : Closed ULC.testClosed2
prfClosed2 = Refl

equivα : (x : Λ) -> (s, r : V) -> (prf : Not (Elem s (fv x))) -> Λ
equivα (Var x) s r prf   = if x == s then (Var r) else (Var x)
equivα (App x y) s r prf = 
  let prf1 = notElemAppLeft (fv y) prf
      prf2 = notElemAppRight (fv x) prf
  in App (equivα x s r prf1) (equivα y s r prf2)
equivα (Abs x y) s r prf = if x == s
                           then Abs r (equivα y s r ?t1)
                           else Abs x (equivα y s r ?t2)



main : IO ()
main = do
  putStrLn $ show $ fv testFreeVar
  putStrLn $ show $ fv testFreeVar2

