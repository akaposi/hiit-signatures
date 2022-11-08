{-# language UnicodeSyntax #-}

{-|
A couple of examples.

Load this module in ghci, and entr "hiitToAgda example" to check the HIIT definitions and
get the types of induction methods and eliminators as Agda output.

-}

module Examples where

import Impl

nat ∷ String
nat = "constructors Nat: U; zero: Nat; suc: Nat;"

fin ∷ String
fin =
     "assume        Nat: U; zero: Nat; suc: Nat → Nat;"
  ++ "constructors  Fin: Nat → U; fzero: (n : Nat) → Fin (suc n); fsuc: (n: Nat) → Fin n → Fin (suc n);"

vec ∷ String
vec =
     "assume Nat: U; zero: Nat; suc: Nat → Nat; A: U;"
  ++ "constructors Vec: Nat → U; nil: Vec zero; cons: (n: Nat) → A → Vec n → Vec (suc n);"

-- | A fragment of an inductive-inductive type theory syntax.
conTyTm ∷ String
conTyTm =
     "constructors "
  ++ "Con: U; Ty: (Γ : Con) → U; Tm: (Γ: Con)(A : Ty Γ) → U;"
  ++ "nil: Con; cons: (Γ : Con) → Ty Γ → Con;"
  ++ "u: (Γ : Con) → Ty Γ; El: (Γ : Con) → Tm Γ (u Γ) → Ty Γ;"

wType ∷ String
wType =
     "assume S: U; P : S → U;"
  ++ "constructors W: U; con: (s: S) → (P s → W) → W;"

ixWType ∷ String
ixWType =
     "assume "
  ++ "  I   : U;"
  ++ "  S   : U;"
  ++ "  P   : S → U;"
  ++ "  Out : S → I;"
  ++ "  In  : (s : S) → P s → I;"
  ++ "constructors "
  ++ "  W   : I → U;"
  ++ "  sup : (s : S) → ((p : P s) → W (In s p)) → W (Out s);"

-- | Inductive-inductive dense completion of a relation.
denseCompletion ∷ String
denseCompletion =
     "assume "
  ++   "A : U;"
  ++   "R : A → A → U;"
  ++ "constructors "
  ++   "Ac : U;"
  ++   "Rc : Ac → Ac → U;"
  ++   "inj: A → Ac;"
  ++   "mid: (x y : Ac) → Rc x y → Ac;"
  ++   "injR: (x y : A) → R x y → Rc (inj x) (inj y);"
  ++   "midl: (x y : Ac)(p : Rc x y) → Rc x (mid x y p);"
  ++   "midr: (x y : Ac)(p : Rc x y) → Rc (mid x y p) y;"

s1 ∷ String
s1 = "constructors S¹: U; base: S¹; loop: Id base base;"

s2 ∷ String
s2 = "constructors S²: U; base: S²; surf: Id (refl base) (refl base);"

interval ∷ String
interval = "constructors I: U; left: I; right: I; seg: Id left right;"

propTrunc ∷ String
propTrunc =
     "assume A: U;"
  ++ "constructors T: U; emb: A → T; trunc: (t u: T) → Id t u;"

setTrunc ∷ String
setTrunc =
     "assume A: U;"
  ++ "constructors T: U; emb: A → T; trunc: (t u: T)(p q: Id t u) → Id p q;"

torus ∷ String
torus =
     "constructors"
  ++ "  T: U;"
  ++ "  b: T;"
  ++ "  p: Id b b;"
  ++ "  q: Id b b;"
  ++ "  t: Id (J (x._. Id b x) p q) (J (x._. Id b x) q p);  "

cauchyReal ∷ String
cauchyReal =
     "assume "
  ++ "  Q: U; "
  ++ "  plus: Q → Q → Q;"
  ++ "  neg: Q → Q;"
  ++ "  lt: Q → Q → U;"
  ++ "constructors "
  ++ "  R: U; "
  ++ "  Rel: Q → R → R → U; "
  ++ "  rat: Q → R;"
  ++ "  lim: (seq: Q → R) → ((δ ε : Q) → Rel (plus δ ε) (seq δ) (seq ε)) → R;"
  ++ "  eqR: (u v: R) → ((ε : Q) → Rel ε u v) → Id u v;"
  ++ "  ratRat: (q r ε : Q) → lt (neg ε) (plus q (neg r)) → lt (plus q (neg r)) ε → Rel ε (rat q) (rat r);"
  ++ "  ratLim: (q ε δ : Q)(y : Q → R)(py : (δ₁ ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))"
  ++ "           → Rel (plus ε (neg δ)) (rat q) (y δ) → Rel ε (rat q) (lim y py);"
  ++ "  limRat: (q ε δ : Q)(y : Q → R)(py : (δ₁ ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))"
  ++ "           → Rel (plus ε (neg δ)) (y δ) (rat q) → Rel ε (lim y py)(rat q);"
  ++ "  limLim: (ε δ η : Q)(y : Q → R)(py : (δ₁ ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))"
  ++ "                     (x : Q → R)(px : (δ₁ ε₁ : Q) → Rel (plus δ₁ ε₁) (x δ₁) (x ε₁))"
  ++ "           → Rel (plus ε (plus (neg δ) (neg η))) (x δ) (y η) → Rel ε (lim x px) (lim y py);"
  ++ "  trunc: (u v : R)(ε : Q)(p q : Rel ε u v) → Id p q;"

-- Examples for erroneous inputs
--------------------------------------------------------------------------------

negativeError ∷ String
negativeError =
  "constructors Neg: U; con: (Neg → Neg) → Neg;"

typeError ∷ String
typeError =
     "assume        Nat: U; zero: Nat; suc: Nat → Nat;"
  ++ "constructors  Fin: Nat → U; fzero: (n : Nat) → Fin (suc n); fsuc: (n: Nat) → Fin → Fin (suc n);"

notFunError ∷ String
notFunError =
  "assume Nat : U; f : Nat; x : f f; constructors Empty: U;"

notFunError2 ∷ String
notFunError2 =
  "constructors A: U; B: A → U; con: A → B U;"

jError1 ∷ String
jError1 =
  "assume A : U; B : U; a : A; b: B; p : Id A B; q: Id (J (x._.x) a a) b; constructors Empty:U;"

jError2 ∷ String
jError2 =
  "assume A : U; B : U; a : A; b: B; p : Id A B; q: Id (J (x._.B) a p) b; constructors Empty:U;"
