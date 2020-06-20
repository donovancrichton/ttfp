module ULC

%default total


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
|||  (1) (Basis) sub(x) = {x}, for each x∈Λ.
|||  (2) (Application) sub((M N)) = sub(M) ⋃ sub(N) ⋃ {(M N)}.
|||  (3) (Abstraction) sub((λx.M)) = sub(M) ⋃ {(λx.M)}.
sub : Λ -> Multiset Λ
sub (Var x) = [Var x]
sub (App m n) = [App m n] ++ sub m ++ sub n
sub (Abs x m) = [Abs x m] ++ sub m

||| A constructive proof that ∀x.P(x) holds where x∈X.
|||  Let X denote {x₂, ..., xₙ}.
|||  (1) (Vacuous) ∀x.P(x) ≡ ⊤ where x∈Ø.
|||  (2) (Union) P(x₁) ≡ ⊤ ∧ ∀x.P(x) ≡ ⊤, x∈X ⇒ ∀x.P(x) ≡ ⊤, x∈x₁⋃X.
data All : {a : Type} -> (P : a -> Type) -> Multiset a -> Type where
  Nil : {P : a -> Type} -> All P []
  (::) : {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
         P x -> All P xs -> All P (x :: xs)

||| A constructive proof that ∃x.P(x) holds where x∈X.
|||  Let X denote {x₂, ..., xₙ}.
|||  (1) (Basis) P(x₁) ≡ ⊤ ⇒ ∃x.P(x), x∈x₁⋃X.
|||  (2) (Union) ∃x.P(x) ≡ ⊤, x∈X ⇒ ∃x.P(x) ≡ ⊤, x∈x₁⋃X.
data Any : {a : Type} -> (P : a -> Type) -> Multiset a -> Type where
  Here : {a : Type} -> {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
         P x -> Any P (x :: xs)
  There : {a : Type} -> {x : a} -> {P : a -> Type} -> {xs : Multiset a} -> 
          Any P xs -> Any P (x :: xs)

||| A constructive proof that x∈X.
In : {a : Type} -> (x : a) -> (xs : Multiset a) -> Type
In x xs = Any (\y => x = y) xs

||| Proof that x∈X where X ≡ Ø ⇒ ⊥.
notInEmpty : Not (In x [])
notInEmpty (Here _) impossible
notInEmpty (There _) impossible

||| Proof that ∃x. x∈X where X ≡ Ø ⇒ ⊥.
notAnyEmpty : {P : a -> Type} -> Not (Any P [])
notAnyEmpty (Here _) impossible
notAnyEmpty (There _) impossible

||| Proof that ∃x. x∈X ⇒ x∈X⋃Y. (For ordered multisets)
inLeftApp : (xs, ys : Multiset a) -> (prf : In x xs) -> In x (xs ++ ys)
inLeftApp xs [] prf = rewrite appendNilRightNeutral xs in prf
inLeftApp [] (y :: ys) prf = void (notInEmpty prf)
inLeftApp (x :: xs) (y :: ys) (Here p) = Here p
inLeftApp (x :: xs) (y :: ys) (There p) = 
  let rec = inLeftApp (xs) (y :: ys) p
  in There rec

||| Proof that ∃x. x∈X ⇒ x∈Y⋃X. (For ordered multisets)
inRightApp : (xs, ys : Multiset a) -> (prf : In x xs) -> In x (ys ++ xs) 
inRightApp [] [] prf = prf
inRightApp [] (x :: xs) prf = void (notInEmpty prf)
inRightApp (x :: xs) [] prf = prf
inRightApp (x :: xs) (y :: ys) prf = 
  let rec = inRightApp (x :: xs) ys prf
  in There rec

||| Proof that x∈X ∨ x∈Y ⇒ x∈X⋃Y.
inEitherLorRimpliesInApp : (i : a) -> (xs, ys : Multiset a) -> 
                           Either (In i xs) (In i ys) -> In i (xs ++ ys)
inEitherLorRimpliesInApp i [] [] (Left p) = p
inEitherLorRimpliesInApp i [] (y :: ys) (Left p) = void (notAnyEmpty p)
inEitherLorRimpliesInApp i [] ys (Right p) = p
inEitherLorRimpliesInApp i (x :: xs) [] (Left p) = 
  let lemma1 = appendNilRightNeutral (x :: xs)
  in rewrite lemma1 in p
inEitherLorRimpliesInApp i (x :: xs) [] (Right p) = void (notAnyEmpty p)
inEitherLorRimpliesInApp i p@(x :: xs) q@(y :: ys) (Left l) = inLeftApp p q l 
inEitherLorRimpliesInApp i (x :: xs) (y :: ys) (Right r) = 
  inRightApp (y :: ys) (x :: xs) r

||| Proof that x∈X⋃Y ⇒ x∈X ∨ x∈Y.
inAppImpliesLorR : (i : a) -> (xs, ys : Multiset a) -> In i (xs ++ ys) -> 
                   Either (In i xs) (In i ys)
inAppImpliesLorR i [] ys prf = Right prf
inAppImpliesLorR i (k :: ks) js (Here x) = Left (Here x)
inAppImpliesLorR i (k :: ks) js (There x) = 
  let rec = inAppImpliesLorR i ks js x
  in case rec of
       Left r => Left (There r)
       Right l => Right l

||| Reflexivity Lemma. ∀x∈Λ. x∈sub(x).
reflSubλ : (x : Λ) -> In x (sub x)
reflSubλ (Var x) = Here Refl
reflSubλ (App x y) = Here Refl
reflSubλ (Abs x y) = Here Refl

||| Transitivity Lemma. x∈sub(y) ∧ y∈sub(z) ⇒ x∈sub(z).
transSubλ : (x, y, z : Λ) -> (prf1: In x (sub y)) -> 
             (prf2 : In y (sub z)) -> In x (sub z)
transSubλ (Var x) (Var y) (Var z) (Here w) (Here s) = 
  let p1 = trans w s
  in rewrite p1 in Here Refl
transSubλ (Var x) (Var y) (Var z) (Here w) (There s) = 
  rewrite w in There s
transSubλ (Var x) (Var y) (Var z) (There w) prf2 = There w
transSubλ (Var x) (Var y) (App z w) (Here s) (Here t) = 
  let p1 = trans s t
  in rewrite p1 in Here Refl
transSubλ (Var x) (Var y) (App z w) (Here s) (There t) = 
  rewrite s in There t
transSubλ (Var x) (Var y) (App z w) (Here s) prf2 = 
  rewrite s in prf2
transSubλ (Var x) (Var y) (App z w) (There s) prf2 impossible
transSubλ (Var x) (Var y) (Abs z w) (Here s) prf2 = 
  rewrite s in prf2
transSubλ (Var x) (Var y) (ULC.Abs z w) (There s) prf2 impossible
transSubλ (Var x) (App y w) (Var z) (Here s) prf2 =
  rewrite s in prf2
transSubλ (Var x) (App y w) (Var z) (There s) (Here t) = 
  Here $ void (uninhabited t)
transSubλ (Var x) (App y w) (Var z) (There s) (There t) impossible
transSubλ (Var x) (App y w) (App z s) (Here t) prf2 = void (uninhabited t)
transSubλ (Var x) (App y w) (App z s) (There t) (Here u) =
  let p1 = fst $ appInjective u
      p2 = snd $ appInjective u
      p3 = replace {P = \k => Any (\y1 => Var x = y1) (sub k ++ sub w)} p1 t
      p4 = replace {P = \k => Any (\y1 => Var x = y1) (sub z ++ sub k)} p2 p3
  in There p4
transSubλ (Var x) (App y w) (App z s) (There t) (There u) = There ?test
transSubλ (Var x) (App y w) (Abs z s) prf1 prf2 = ?test_5
transSubλ (Var x) (Abs y w) z prf1 prf2 = ?test_6
transSubλ (App x w) y z prf1 prf2 = ?test_2
transSubλ (Abs x w) y z prf1 prf2 = ?test_3


testExp : Λ
testExp = Abs "x" (Var "y") 



main : IO ()
main = do
  putStrLn $ show testExp
  putStrLn $ show $ sub testExp
