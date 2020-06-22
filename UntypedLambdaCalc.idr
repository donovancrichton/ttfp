module ULC

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
Uninhabited (ULC.Var x = ULC.App y z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. App(x, y) ≡ Var(z) ⇒ ⊥.
Uninhabited (ULC.App x y = ULC.Var z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Var(x) ≡ Abs(y, z) ⇒ ⊥.
Uninhabited (ULC.Var x = ULC.Abs y z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Abs(x, y) ≡ Var(z) ⇒ ⊥.
Uninhabited (ULC.Abs x y = ULC.Var z) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. App(x, y) ≡ Abs(z, w) ⇒ ⊥.
Uninhabited (ULC.App x y = ULC.Abs z w) where
  uninhabited Refl impossible

||| Proof that ∀x, y, z. Abs(x, y) ≡ App(z, w) ⇒ ⊥.
Uninhabited (ULC.Abs x y = ULC.App z w) where
  uninhabited Refl impossible

||| Proof that App(x, y) ≡ App(q, r) -> x ≡ q ∧ y ≡ r.
appInjective : (prf : ULC.App x y = ULC.App q r) -> (x = q, y = r)
appInjective Refl = (Refl, Refl)

||| Proof that Abs(x, y) ≡ Abs(q, r) -> x ≡ q ∧ y ≡ r.
absInjective : (prf : ULC.Abs x y = ULC.Abs q r) -> (x = q, y = r)
absInjective Refl = (Refl, Refl)

-- pretty printing for untyped λ calculus.
implementation Show Λ where
  show (Var x) = x
  show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
  show (Abs x m) = "(λ" ++ x ++ "." ++ show m ++ ")"

||| Multiset of subterms of Λ.
|||  Let V denote a set of symbols.
|||  (1) (Variable) sub(x) = {x}, for each x∈V.
|||  (2) (Application) sub((M N)) = sub(M) ⋃ sub(N) ⋃ {(M N)}.
|||  (3) (Abstraction) sub((λx.M)) = sub(M) ⋃ {(λx.M)}.
sub : Λ -> Multiset Λ
sub (Var x) = [Var x]
sub (App m n) = [App m n] ++ sub m ++ sub n
sub (Abs x m) = [Abs x m] ++ sub m

||| A constructive proof that ∀x.P(x) holds where x∈X.
|||  Let X denote {x₂, ..., xₙ}.
|||  (1) (Vacuous) ∀x.P(x) ≡ ⊤ where x∈Ø.
|||  (2) (Induction) P(x₁) ≡ ⊤ ∧ ∀x.P(x) ≡ ⊤, x∈X ⇒ ∀x.P(x) ≡ ⊤, x∈x₁⋃X.
data All : {a : Type} -> (P : a -> Type) -> Multiset a -> Type where
  Nil : {P : a -> Type} -> All P []
  (::) : {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
         P x -> All P xs -> All P (x :: xs)

||| A constructive proof that ∃x.P(x) holds where x∈X.
|||  Let X denote {x₂, ..., xₙ}.
|||  (1) (Union) P(x₁) ≡ ⊤ ⇒ ∃x.P(x), x∈x₁⋃X.
|||  (2) (Induction) ∃x.P(x) ≡ ⊤, x∈X ⇒ ∃x.P(x) ≡ ⊤, x∈x₁⋃X.
data Any : {a : Type} -> (P : a -> Type) -> Multiset a -> Type where
  Here : {a : Type} -> {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
         P x -> Any P (x :: xs)
  There : {a : Type} -> {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
          Any P xs -> Any P (x :: xs)

||| Proof that ∃x∈X.P(x) where X = Ø ⇒ ⊥.
Uninhabited (Any p []) where
  uninhabited prf impossible

||| Proof that if X ≠ Ø and ∀x∈X.P(x) ≡ ⊤ then ∃x∈X.P(x) ≡ ⊤ must follow.
allImpliesAny : {a : Type} -> {P : a -> Type} -> {xs : Multiset a} -> 
                (prf1 : NonEmpty xs) -> (prf2 : All P xs) -> Any P xs
allImpliesAny prf1 [] = absurd prf1
allImpliesAny prf1 (x :: xs) = Here x

||| Proof that ∃x∈X.P(x) ≡ ⊤ ⇒ X ≠ Ø.
anyImpliesNonEmpty : {P : a -> Type} -> (prf : Any P xs) -> NonEmpty xs  
anyImpliesNonEmpty (Here p) = IsNonEmpty
anyImpliesNonEmpty (There p) = IsNonEmpty

||| A constructive proof that x∈X.
In : {a : Type} -> (x : a) -> (xs : Multiset a) -> Type
In x xs = Any (\y => x = y) xs

||| Proof that ∃x. x∈X ⇒ x∈X⋃Y. (For ordered multisets)
inLeftApp : (xs, ys : Multiset a) -> (prf : In x xs) -> In x (xs ++ ys)
inLeftApp xs [] prf = rewrite appendNilRightNeutral xs in prf
inLeftApp [] (y :: ys) prf = absurd prf
inLeftApp (x :: xs) (y :: ys) (Here p) = Here p
inLeftApp (x :: xs) (y :: ys) (There p) = 
  let ih = inLeftApp (xs) (y :: ys) p
  in There ih

||| Proof that ∃x. x∈X ⇒ x∈Y⋃X. (For ordered multisets)
inRightApp : (xs, ys : Multiset a) -> (prf : In x xs) -> In x (ys ++ xs) 
inRightApp [] [] prf = prf
inRightApp [] (x :: xs) prf = absurd prf
inRightApp (x :: xs) [] prf = prf
inRightApp (x :: xs) (y :: ys) prf = 
  let ih = inRightApp (x :: xs) ys prf
  in There ih

||| Proof that x∈X ∨ x∈Y ⇒ x∈X⋃Y.
inEitherLorRimpliesInApp : (i : a) -> (xs, ys : Multiset a) -> 
                           Either (In i xs) (In i ys) -> In i (xs ++ ys)
inEitherLorRimpliesInApp i [] [] (Left p) = p
inEitherLorRimpliesInApp i [] (y :: ys) (Left p) = absurd p
inEitherLorRimpliesInApp i [] ys (Right p) = p
inEitherLorRimpliesInApp i (x :: xs) [] (Left p) = 
  let lemma1 = appendNilRightNeutral (x :: xs)
  in rewrite lemma1 in p
inEitherLorRimpliesInApp i (x :: xs) [] (Right p) = absurd p
inEitherLorRimpliesInApp i p@(x :: xs) q@(y :: ys) (Left l) = inLeftApp p q l 
inEitherLorRimpliesInApp i (x :: xs) (y :: ys) (Right r) = 
  inRightApp (y :: ys) (x :: xs) r

||| Proof that x∈X⋃Y ⇒ x∈X ∨ x∈Y.
inAppLR : (i : a) -> (xs, ys : Multiset a) -> In i (xs ++ ys) -> 
                   Either (In i xs) (In i ys)
inAppLR i [] ys prf = Right prf
inAppLR i (k :: ks) js (Here x) = Left (Here x)
inAppLR i (k :: ks) js (There x) = 
  let ih = inAppLR i ks js x
  in case ih of
       Left r => Left (There r)
       Right l => Right l


||| Reflexivity Lemma. ∀x∈Λ. x∈sub(x).
reflSubλ : (x : Λ) -> In x (sub x)
reflSubλ (Var x) = Here Refl
reflSubλ (App x y) = Here Refl
reflSubλ (Abs x y) = Here Refl

||| Proof that ∀z. Abs(x, y)∈sub(z) ⇒ y∈sub(z).
absRightArg : (y, z : Λ) -> (prf : In (Abs x y) (sub z)) -> In y (sub z)
absRightArg y (Var x) (Here p) = absurd p
absRightArg y (Var x) (There p) = absurd p
absRightArg y (App j k) (Here p) = absurd p
absRightArg {x} y (App j k) (There p) with
  (inAppLR (Abs x y) (sub j) (sub k) p)
    | (Left l) = 
      let ih = absRightArg y j l
          p1 = inLeftApp (sub j) (sub k) ih
      in There p1
    | (Right r) = 
      let ih = absRightArg y k r
          p1 = inRightApp (sub k) (sub j) ih
      in There p1
absRightArg y (Abs x z) (Here p) = 
  let p1 = snd $ absInjective p
      p2 = reflSubλ y
  in rewrite sym p1 in There p2
absRightArg y (Abs x z) (There p) = 
  let ih = absRightArg y z p
  in There ih

||| Proof that ∀z. App(x, y)∈sub(z) ⇒ x∈sub(z).
appLeftArg : (x, z : Λ) -> (prf : In (App x y) (sub z)) -> In x (sub z)
appLeftArg x (Var y) (Here p) = absurd p
appLeftArg x (Var y) (There p) = absurd p
appLeftArg x (App q r) (Here p) = 
  let p1 = fst $ appInjective p
      p2 = reflSubλ x
      p3 = inLeftApp (sub x) (sub r) p2
  in rewrite sym p1 in There p3
appLeftArg {y} x (App j k) (There p) with (inAppLR (App x y) (sub j) (sub k) p)
  | (Left l) = let ih = appLeftArg x j l
                   p1 = inLeftApp (sub j) (sub k) ih
               in There p1
  | (Right r) = let ih = appLeftArg x k r
                    p1 = inRightApp (sub k) (sub j) ih
                in There p1
appLeftArg x (Abs j k) (Here p) = absurd p
appLeftArg {y} x (Abs j k) (There p) = 
  let ih = appLeftArg x k p
  in There ih

||| Proof that ∀z. App(x, y)∈sub(z) ⇒ y∈sub(z).
appRightArg : (y, z : Λ) -> (prf : In (App x y) (sub z)) -> In y (sub z)
appRightArg y (Var x) (Here p) = absurd p
appRightArg y (Var x) (There p) = absurd p
appRightArg y (App j k) (Here p) = 
  let p1 = snd $ appInjective p
      p2 = reflSubλ y
      p3 = inRightApp (sub y) (sub j) p2
  in rewrite sym p1 in There p3
appRightArg {x} y (App j k) (There p) with 
  (inAppLR (App x y) (sub j) (sub k) p)
    | (Left l) = let ih = appRightArg y j l
                     p1 = inLeftApp (sub j) (sub k) ih
                 in There p1
    | (Right r) = let ih = appRightArg y k r
                      p1 = inRightApp (sub k) (sub j) ih
                  in There p1
appRightArg y (Abs j k) (Here p) = absurd p
appRightArg y (Abs j k) (There p) = 
  let ih = appRightArg y k p
  in There ih

||| Transitivity Lemma. x∈sub(y) ∧ y∈sub(z) ⇒ x∈sub(z).
transSubλ : (x, y, z : Λ) -> (prf1: In x (sub y)) -> 
             (prf2 : In y (sub z)) -> In x (sub z)
transSubλ (Var x) (Var y) (Var z) (Here w) prf2 = 
  rewrite w in prf2
transSubλ (Var x) (Var y) (Var z) (There w) prf2 = absurd w
transSubλ (Var x) (Var y) (App z w) (Here s) (Here t) = absurd t
transSubλ (Var x) (Var y) (App z w) (Here s) (There t) = 
  rewrite s in There t
transSubλ (Var x) (Var y) (App z w) (There s) prf2 = absurd s
transSubλ (Var x) (Var y) (Abs z w) (Here s) prf2 = 
  rewrite s in prf2
transSubλ (Var x) (Var y) (Abs z w) (There s) prf2 = absurd s
transSubλ (Var x) (App y w) (Var z) (Here s) prf2 = absurd s
transSubλ (Var x) (App y w) (Var z) (There s) (Here t) = absurd t
transSubλ (Var x) (App y w) (Var z) (There s) (There t) = absurd t
transSubλ (Var x) (App y w) (App q r) (Here s) prf2 = absurd s
transSubλ (Var x) (App y w) (App q r) (There s) (Here t) = 
  let p1 = appInjective t
  in rewrite sym (fst p1) in rewrite sym (snd p1) in There s
transSubλ (Var x) (App y w) (App j k) (There s) (There t) with
  ((inAppLR (Var x) (sub y) (sub w) s), (inAppLR (App y w) (sub j) (sub k) t))
    | (Left l, Left l') = 
      let p1 = appLeftArg y j l'
          ih = transSubλ (Var x) y j l p1
          p2 = inLeftApp (sub j) (sub k) ih
      in There p2
    | (Left l, Right r) = 
      let p1 = appLeftArg y k r
          ih = transSubλ (Var x) y k l p1
          p2 = inRightApp (sub k) (sub j) ih
      in There p2
    | (Right r, Left l) = 
      let p1 = appRightArg w j l
          ih = transSubλ (Var x) w j r p1
          p2 = inLeftApp (sub j) (sub k) ih
      in There p2
    | (Right r, Right r') =
      let p1 = appRightArg w k r'
          ih = transSubλ (Var x) w k r p1
          p2 = inRightApp (sub k) (sub j) ih
      in There p2
transSubλ (Var x) (App y w) (Abs j k) (Here p) prf2 = absurd p
transSubλ (Var x) (App y w) (Abs j k) (There p) (Here s) = absurd s
transSubλ (Var x) (App y w) (Abs j k) (There p) (There s) with
  (inAppLR (Var x) (sub y) (sub w) p)
    | (Left l) = 
      let p1 = appLeftArg y k s
          ih = transSubλ (Var x) y k l p1
      in There ih
    | (Right r) = 
      let p1 = appRightArg w k s
          ih = transSubλ (Var x) w k r p1
      in There ih
transSubλ (Var x) (Abs y w) z (Here s) prf2 = absurd s
transSubλ (Var x) (Abs y w) z (There s) prf2 = 
  let p1 = absRightArg w z prf2
      ih = transSubλ (Var x) w z s p1
  in ih
transSubλ (App x y) (Var w) z (Here p) prf2 = absurd p
transSubλ (App x y) (Var w) z (There p) prf2 = absurd p
transSubλ (App x y) (App j k) z (Here p) prf2 = 
  rewrite p in prf2
transSubλ (App x y) (App j k) z (There p) prf2 with
  (inAppLR (App x y) (sub j) (sub k) p)
    | (Left l) = 
      let p1 = appLeftArg j z prf2
          ih = transSubλ (App x y) j z l p1
      in ih
    | (Right r) = 
      let p1 = appRightArg k z prf2
          ih = transSubλ (App x y) k z r p1
      in ih
transSubλ (App x y) (Abs j k) z (Here p) prf2 = absurd p
transSubλ (App x y) (Abs j k) z (There p) prf2 = ?test
transSubλ (Abs x w) y z prf1 prf2 = ?transSubλ_rhs_3

testExp : Λ
testExp = Abs "x" (Var "y") 



main : IO ()
main = do
  putStrLn $ show testExp
  putStrLn $ show $ sub testExp
