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
  Here : {a : Type} -> {P : a -> Type} -> {xs : Multiset a} -> 
         P x -> Any P (x :: xs)
  There : {a : Type} -> {P : a -> Type} -> {xs : Multiset a} -> 
          Any P xs -> Any P (x :: xs)

||| A constructive proof that x∈X.
In : {a : Type} -> (x : a) -> (xs : Multiset a) -> Type
In x xs = Any (\y => x = y) xs

||| Reflexivity Lemma. ∀x∈Λ. x∈sub(x).
reflexivity : (x : Λ) -> In x (sub x)
reflexivity (Var x) = Here Refl
reflexivity (App x y) = Here Refl
reflexivity (Abs x y) = Here Refl

||| Transitivity Lemma. x∈sub(y) ∧ y∈sub(z) ⇒ x∈sub(z).
transitivity : (x, y, z : Λ) ->
               (prf1: In x (sub y)) -> (prf2 : In y (sub z)) -> In x (sub z)
transitivity (Var x) (Var y) (Var z) (Here w) (Here s) = 
  let p1 = trans w s
  in rewrite p1 in Here Refl
transitivity (Var x) (Var y) (Var z) (Here w) (There s) = 
  rewrite w in There s
transitivity (Var x) (Var y) (Var z) (There w) prf2 = ?test
transitivity (Var x) (Var y) (App z w) prf1 prf2 = ?test_7
transitivity (Var x) (Var y) (Abs z w) prf1 prf2 = ?test_8
transitivity (Var x) (App y w) z prf1 prf2 = ?test_5
transitivity (Var x) (Abs y w) z prf1 prf2 = ?test_6
transitivity (App x w) y z prf1 prf2 = ?test_2
transitivity (Abs x w) y z prf1 prf2 = ?test_3


testExp : Λ
testExp = Abs "x" (Var "y") 



main : IO ()
main = do
  putStrLn $ show testExp
  putStrLn $ show $ sub testExp
