# elims-demo

This package contains a type checker and eliminator-generator for
higher inductive-inductive (HIIT) definitions, based on the paper "A
Syntax for Higher Inductive-Inductive Types" by Ambrus Kaposi and
András Kovács. It validates HIIT definitions, then generates types of
induction methods, eliminators and β-rules in an Agda-checkable
format.

## Installation

Install [stack](https://docs.haskellstack.org/en/stable/README/), then
hit `stack install` in the project directory. You may need to do
`stack setup` first if you don't have the required GHC version
installed.

You might also want
[Agda](https://agda.readthedocs.io/en/v2.5.3/getting-started/installation.html)
installed, if you want to typecheck the generated output. Any
non-ancient Agda version would work. The easiest way to do this is by
`stack install Agda`.

## Usage

After installation, invoke `hiit-defs example.hiit` to generate Agda
output. There are a number of examples in `/examples`. Alternatively,
you can hit `stack ghci` in the program directory, then `:l
Examples.hs`, to experiment in a REPL manner.

## Quick example

You can write a HIIT definition in a file, say `circle.hiit`, like this:

```
constructors
  S¹     : U;
  base   : S¹;
  loop   : Id base base;
```

Then hit `hiit-defs circle.hiit` to get the following printed:

```
-- Agda header
U = Set

infix 4 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
  refl : x ≡ x

J : ∀{α β}{A : Set α} {a₀ : A} (P : (a₁ : A) → a₀ ≡ a₁ → Set β) → P _ refl → ∀ {a₁}(p : a₀ ≡ a₁) → P a₁ p
J P pr refl = pr

tr : ∀{α β}{A : Set α}(B : A → Set β){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B eq t = J (λ x _ → B x) t eq

apd : ∀ {α β}{A : Set α}{B : A → Set β}(f : ∀ a → B a){x y : A}(p : x ≡ y) → tr B p (f x) ≡ f y
apd {A = A} {B} f {t} {u} p = J (λ y p → tr B p (f t) ≡ f y) (refl {x = f t}) p

postulate
  -- Constructors:
  S¹ : U
  base : S¹
  loop : base ≡ base

  -- Induction methods:
  S¹ᴹ : S¹ → U
  baseᴹ : S¹ᴹ base
  loopᴹ : tr S¹ᴹ loop baseᴹ ≡ baseᴹ

  -- Eliminators and β-rules:
  S¹ᴱ : (x' : S¹) → S¹ᴹ x'
  baseᴱ : S¹ᴱ base ≡ baseᴹ
  loopᴱ : tr (λ u' → tr S¹ᴹ loop u' ≡ baseᴹ) baseᴱ
            (tr (λ u' → tr S¹ᴹ loop (S¹ᴱ base) ≡ u') baseᴱ
              (apd S¹ᴱ loop)) ≡ loopᴹ
```

To explain the output:

  - First, there is an Agda header defining propositional equality,
    `J` and transport.
  - Then, we postulate constructors, induction methods and finally
    eliminators/β-rules.
    - In a more categorical language, we could call the three
      postulated sections "algebras", "dependent algebras", and
      "dependent algebra sections", borrowing terminology from
      [Shulman](https://www.youtube.com/watch?v=4SLbgT-CfRM).
    - The actual type of the induction principle would be a dependent
      function from all induction methods to a Σ-type/record
      containing all eliminators and β-rules.

  - Notice the type for `loopᴱ`. It is more complicated than the usual
    definition in HoTT because all of our β-rules are only
    propositional equalities. Hence, β-rules may need to be
    transported along previous β-rules in order to be well-typed.
    Such transporting can be necessary for inductive-inductive types
    without any higher constructors; see `examples/conTyTm.hiit` for
    such an example.

## HIIT syntax in more detail

#### Sections

A HIIT definition consists of an optional `assume` section followed by
a mandatory non-empty `constructors` section. In both sections, types
must be terminated by semicolons (`;`).

Note that name shadowing is currently disallowed.

The `assume` section contains names with types, which are assumed to
come from an otherwise unspecified ambient type theory. These names
are not part of the inductive part of the HIIT definition. In the
parlance of the "A Syntax for Higher Inductive-Inductive Types", this
section is the "target theory" context.

For an example, we may define lists containing elements of an arbitrary
type coming from the ambient type theory:

```
assume
  A : U;
constructors
  List : U;
  nil  : List;
  cons : A → List → List;
```

Or we can define W-types which refer to shapes and positions:

```
assume
  S : U;
  P : S → U;
constructors
  W   : U;
  con : (s : S) → (P s → W) → W;
```
Assumptions can serve as "parameters" to the HIIT, but you can also
think of them as any kind of _a priori_ existing definitions.

The `constructors` section specifies inductive constructors. In the
paper's terminology, this section is a Γ context in the "source"
theory, or the theory of HIIT codes.

Here, only strictly positive definitions are allowed, so `constructors T: U;
con: (T → T) → T;` is invalid, for instance.

#### Types

Types are specified with a small type theory, which contains:

  - A universe `U`.
  - Dependent functions denoted `(x : A) → B` or `A → B` when non-dependent.
    - You can group arguments like `(x y z : A) → B`.
    - And also drop arrows: `(x : A)(y : B) → C`.
    - And use non-unicode syntax: `(x : A) -> B`.
  - Identity types `Id t u`.
    - The type of `t` and `u` is inferred. Currently, it cannot be explicitly provided.
    - We have `refl t : Id t t`. Again, the type of `t` can't be given explicitly.
    - We have path induction `J (x.y.p) pr eq`, where `eq : Id t u`,
      with `t : a` and `u : a` for some `a`, `p : U` (assuming `x : a`
      and `y : Id t x`), and `pr : p [x ⊢> t, y ⊢> refl t]`. Again,
      other parameters to `J` can't be explicitly given.
  - There are no lambda expressions currently.

#### Differences to the paper

First, the paper has Tarski-style universes with explicit decoding
(El). `hiit-defs` doesn't have explicit decoding in the surface
syntax, but it does have them in the internal "core" syntax. It uses
type-directed elaboration to fill in a number of details, including
El-s, in order to be more user-friendly, so this is only a surface
difference.

There are two actual differences to the paper.

  - The non-inductive "target" theory has a cumulative universe hierarchy
    in the paper. Here, we have type-in-type, purely because of ease of
    implementation, and thus we only eliminate into `U` instead of a universe
    at a user-given level. This is probably not a big issue, since we can
    easily spot universe consistency issues by checking the output in Agda.
  - The paper has a Jβ construction for weakly representing the
    computation rule for J in the inductive "source" syntax. In the
    current implementation, we don't include Jβ, as it doesn't really
    have any use case that we know of. Nonetheless, in the future it may be
    added for the sake of completeness.
