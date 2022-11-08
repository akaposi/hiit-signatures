{-# OPTIONS --without-K --rewriting #-}

{-
Definition of HIIT codes.

We use a shallow embedding where the target theory is represented as
Agda. Hence, we use the Agda function space to represent external non-inductive
dependencies, instead of having a stratified syntax with both an external and an
internal (inductive) typing context.

For example, the non-inductive function space has type formation rule

    ΠNI : ∀ {Γ}(A : Set) → (A → Ty Γ) → Ty Γ

where A is a small type in Agda, and (A → Ty Γ) encodes possible dependencies on
A in the codomain type.
-}

module DeepSourceSyntax where

open import Lib

infixl 5 _▶_
infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t

postulate

-- Base CwF (category with families), i.e. the explicit substitution calculus
--------------------------------------------------------------------------------

  -- Type formers are in Set₁ because terms and types may include things in Set₀
  Con   : Set₁
  Ty    : Con → Set₁
  Tm    : ∀ Γ → Ty Γ → Set₁
  Sub   : Con → Con → Set₁

  ∙     : Con
  _▶_   : (Γ : Con) → Ty Γ → Con

  _[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

  id    : ∀{Γ} → Sub Γ Γ
  _∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  ε     : ∀{Γ} → Sub Γ ∙
  _,s_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  π₁    : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ

  _[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  π₂    : ∀{Γ Δ}{A : Ty Δ}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)

  [id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
  [][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T

  idl   : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
  idr   : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
  ass   : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
        → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

  ,∘    : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
        → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
  π₁β   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → (π₁ (σ ,s t)) ≡ σ
  πη    : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
        → (π₁ σ ,s π₂ σ) ≡ σ
  εη    : ∀{Γ}{σ : Sub Γ ∙}
        → σ ≡ ε
  π₂β   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t

wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs x = x [ wk ]t

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
σ ^ A = (σ ∘ wk) ,s tr (Tm _) [][]T vz

infixl 5 _^_

-- Universe
--------------------------------------------------------------------------------

postulate
  U    : ∀{Γ} → Ty Γ
  U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
  El   : ∀{Γ}(a : Tm Γ U) → Ty Γ
  El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (tr (Tm Γ) U[] (a [ σ ]t)))

-- Inductive functions
--------------------------------------------------------------------------------

  Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ

  Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}
      → (Π a B) [ σ ]T ≡ Π (tr (Tm Γ) U[] (a [ σ ]t))
                           (tr (λ x → Ty (Γ ▶ x)) El[] (B [ σ ^ El a ]T))

  app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B

  app[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))

_$_ : ∀ {Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}(t : Tm Γ (Π a B))(u : Tm Γ (El a)) → Tm Γ (B [ < u > ]T)
t $ u = (app t) [ < u > ]t

-- Non-inductive functions
--------------------------------------------------------------------------------

postulate
  ΠNI : ∀ {Γ}(A : Set) → (A → Ty Γ) → Ty Γ

  ΠNI[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Set}{B : A → Ty Δ}
          → ΠNI A B [ σ ]T ≡ ΠNI A (λ α → B α [ σ ]T)

  appNI : ∀ {Γ}{A}{B : A → Ty Γ} → Tm Γ (ΠNI A B) → (∀ α → Tm Γ (B α))

  appNI[] :  ∀ {Γ Δ}{σ : Sub Γ Δ}{A}{B : A → Ty Δ}(t : Tm Δ (ΠNI A B)) α
             → appNI t α [ σ ]t ≡ appNI (tr (Tm Γ) ΠNI[] (t [ σ ]t)) α

-- Small non-inductive functions (infinitary parameters)
--------------------------------------------------------------------------------

postulate
  Πₙᵢ : ∀ {Γ}(A : Set) → (A → Tm Γ U) → Tm Γ U

  Πₙᵢ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Set}{b : A → Tm Δ U}
          → tr (Tm Γ) U[] (Πₙᵢ A b [ σ ]t) ≡ Πₙᵢ A (λ α → tr (Tm Γ) U[] (b α [ σ ]t))

  appₙᵢ : ∀ {Γ}{A}{b : A → Tm Γ U} → Tm Γ (El (Πₙᵢ A b)) → (∀ α → Tm Γ (El (b α)))

  appₙᵢ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A}{b : A → Tm Δ U}(t : Tm Δ (El (Πₙᵢ A b))) α
          → tr (Tm Γ) El[] (appₙᵢ t α [ σ ]t) ≡ appₙᵢ (tr (Tm Γ) (El[] ◾ ap El Πₙᵢ[]) (t [ σ ]t)) α

-- Identity (with only transport)
--------------------------------------------------------------------------------

postulate
  Id   : ∀ {Γ}(a : Tm Γ U) → Tm Γ (El a) → Tm Γ (El a) → Tm Γ U
  Id[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{t u : Tm Δ (El a)}
         → tr (Tm Γ) (U[]) (Id a t u [ σ ]t) ≡
             (Id (tr (Tm Γ) U[] (a [ σ ]t))
                 (tr (Tm Γ) El[] (t [ σ ]t))
                 (tr (Tm Γ) El[] (u [ σ ]t)))

_^El_ :
  {Γ Δ : Con}(σ : Sub Γ Δ)(a : Tm Δ U)
  → Sub (Γ ▶ El (tr (Tm Γ) U[] (a [ σ ]t))) (Δ ▶ El a)
σ ^El a = σ ∘ wk ,s tr (Tm _) (ap (_[ wk ]T) (El[]  ⁻¹) ◾ ([][]T)) vz

-- _^U_ :
--  ∀ {Γ Δ}(σ : Sub Γ Δ)(a : Tm Δ

infixl 5 _^El_

postulate
  Transp :
    ∀ {Γ}{a : Tm Γ U}(P : Ty (Γ ▶ El a))
      {t u : Tm Γ (El a)}
      (pt : Tm Γ (P [ < t > ]T))
      (eq : Tm Γ (El (Id a t u)))
    → Tm Γ (P [ < u > ]T)

  <>∘El :
    {Γ Δ  : Con}
    (σ  : Sub Γ Δ)
    (a  : Tm Δ U)
    (t  : Tm Δ (El a))
    → < t > ∘ σ ≡ (σ ^El a) ∘ < tr (Tm Γ) El[] (t [ σ ]t) >

  Transp[] :
    ∀ {Γ Δ}{σ : Sub Γ Δ}
      {a : Tm Δ U}(P : Ty (Δ ▶ El a))
      {t u : Tm Δ (El a)}
      (pt : Tm Δ (P [ < t > ]T))
      (eq : Tm Δ (El (Id a t u)))
    → tr (Tm Γ) ([][]T ◾ ap (P [_]T) (<>∘El σ a u) ◾ [][]T ⁻¹)
      (Transp P pt eq [ σ ]t)
      ≡ Transp
          (P [ σ ^El a ]T)
          (tr (Tm Γ) ([][]T ◾ ap (P [_]T) (<>∘El σ a t) ◾ [][]T ⁻¹) (pt [ σ ]t))
          ((tr (Tm Γ) ((El[] {σ = σ} ◾ ap El (Id[] {σ = σ}))) (eq [ σ ]t)))

-- Identity of sorts
--------------------------------------------------------------------------------

postulate
  IdU     : ∀{Γ}(a b : Tm Γ U) → Ty Γ
  IdU[]   : ∀{Γ}{a b : Tm Γ U}{Θ}{σ : Sub Θ Γ} → IdU a b [ σ ]T ≡ IdU (tr (Tm Θ) U[] (a [ σ ]t)) (tr (Tm Θ) U[] (b [ σ ]t))
  reflU   : ∀{Γ}(a : Tm Γ U) → Tm Γ (IdU a a)
  reflU[] : ∀{Γ}{a : Tm Γ U}{Θ}{σ : Sub Θ Γ} → tr (Tm Θ) IdU[] (reflU a [ σ ]t) ≡ reflU (tr (Tm Θ) U[] (a [ σ ]t))
  TranspU : ∀{Γ}{a b : Tm Γ U}(p : Tm (Γ ▶ U) U)(pa : Tm Γ (El p [ < a > ]T))(eq : Tm Γ (IdU a b)) → Tm Γ (El p [ < b > ]T)

  -- <>∘U :
  --   {Γ Δ  : Con}
  --   (σ  : Sub Γ Δ)
  --   (a  : Tm Δ U)
  --   → < a > ∘ σ ≡ (σ ^ U) ∘ < a [ σ ]t >

  -- TranspU[] :
  --   ∀ {Γ Δ}{σ : Sub Γ Δ}{a b : Tm Δ U}(p : Tm (Δ ▶ U) U)(pa : Tm Δ (El p [ < a > ]T))(eq : Tm Δ (IdU a b))
  --   → coe {!!} (TranspU p pa eq [ σ ]t)
  --     ≡ TranspU (coe (ap (Tm (Γ ▶ U [ σ ]T)) U[] ◾ ap (λ x → Tm (Γ ▶ x) U) U[]) (p [ σ ^ U ]t))
  --               (tr (Tm Γ) ([][]T {A = El p} ◾ ap (λ x → El p [ x ]T) (<>∘U σ a) ◾ {!!}) (pa [ σ ]t))
  --               (tr (Tm Γ) IdU[] (eq [ σ ]t))
