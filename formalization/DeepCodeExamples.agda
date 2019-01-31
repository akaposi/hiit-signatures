{-# OPTIONS --without-K #-}

{- Some examples for definitions in the deep source syntax #-}

module DeepCodeExamples where

open import Lib
open import DeepSourceSyntax

-- Shorthands for variables and weakenings with various types
--------------------------------------------------------------------------------

zU : ∀ {Γ} → Tm (Γ ▶ U) U
zU = tr (Tm _) U[] vz

infixl 3 sU_
sU_ : ∀ {Γ A} → Tm Γ U → Tm (Γ ▶ A) U
sU_ t = tr (Tm _) U[] (vs t)

zEl : ∀ {Γ a} → Tm (Γ ▶ El a) (El (sU a))
zEl = tr (Tm _) El[] vz

infixl 3 sEl_
sEl_ : ∀ {Γ a B} → Tm Γ (El a) → Tm (Γ ▶ B) (El (sU a))
sEl_ t = tr (Tm _) El[] (vs t)

zNU : ∀ {Γ A} → Tm (Γ ▶ ΠNI A (λ _ → U)) (ΠNI A (λ _ → U))
zNU = tr (Tm _) (ΠNI[] ◾ ap (ΠNI _) (ext λ _ → U[])) vz

infixl 3 sNU_
sNU_ : ∀ {Γ A C} → Tm Γ (ΠNI A (λ _ → U)) → Tm (Γ ▶ C) (ΠNI A (λ _ → U))
sNU_ t = tr (Tm _) (ΠNI[] ◾ ap (ΠNI _) (ext λ _ → U[])) (vs t)

zId : ∀ {Γ a t u} → Tm (Γ ▶ El (Id a t u)) (El (Id (sU a) (sEl t) (sEl u)))
zId = tr (Tm _) (El[] ◾ ap El Id[]) vz

infixl 3 sId_
sId_ : ∀ {Γ a t u B} → Tm Γ (El (Id a t u)) → Tm (Γ ▶ B) (El (Id (sU a) (sEl t) (sEl u)))
sId_ t = tr (Tm _) (El[] ◾ ap El Id[]) (vs t)

zΠU : ∀ {Γ a} → Tm (Γ ▶ Π a U) (Π (sU a) U)
zΠU {Γ}{a} =
  tr (Tm _)
     (Π[] ◾ ap (Π _) (ap (tr (λ x → Ty (Γ ▶ Π a U ▶ x)) El[]) U[]
          ◾ J (λ _ el[] → tr (λ x → Ty (Γ ▶ Π a U ▶ x)) el[] U ≡ U) refl El[]))
      vz

infixl 3 sΠU_
sΠU_ : ∀ {Γ a B} → Tm Γ (Π a U) → Tm (Γ ▶ B) (Π (sU a) U)
sΠU_ {Γ}{a}{B} t =
  tr (Tm _)
     (Π[] ◾ ap (Π _) (ap (tr (λ x → Ty (Γ ▶ B ▶ x)) El[]) U[]
          ◾ J (λ _ el[] → tr (λ x → Ty (Γ ▶ B ▶ x)) el[] U ≡ U) refl El[] ))
     (vs t)

infixl 7 _$U_
_$U_ : ∀ {Γ a} → Tm Γ (Π a U) → Tm Γ (El a) → Tm Γ U
t $U a = tr (Tm _) U[] (t $ a)


-- Example codes
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool

nat : Con
nat = ∙                        --
  ▶ U                          -- Nat  : U
  ▶ El zU                      -- zero : Nat
  ▶ Π (sU zU) (El (sU sU zU))  -- suc  : Nat → Nat

I : Con
I = ∙
  ▶ U                        -- I     : U
  ▶ El zU                    -- left  : I
  ▶ El (sU zU)               -- right : I
  ▶ El (Id _ (sEl zEl) zEl)  -- seg   : left = right

S¹ : Con
S¹ = ∙
  ▶ U                 -- S¹ : U
  ▶ El zU             -- base : S¹
  ▶ El (Id _ zEl zEl) -- loop : base = base

-- Nat indexed vectors
vec : Set → Con
vec A = ∙
  ▶ ΠNI ℕ (λ _ → U)
  ▶ El (appNI zNU 0)
  ▶ ΠNI ℕ (λ n → ΠNI A (λ _ → Π (appNI (sNU zNU) n) (El (appNI (sNU sNU zNU) (1 + n)))))

-- Propositional equality
Eq : (A : Set) → A → Con
Eq A a = ∙
  ▶ ΠNI A (λ _ → U)
  ▶ El (appNI zNU a)

Eq' : (A : Set) → Con
Eq' A = ∙
  ▶ ΠNI A (λ _ → ΠNI A (λ _ → U))
  ▶ ΠNI A (λ a → El (appNI (tr (Tm _) (ΠNI[] ◾ ap (ΠNI _)
                    (ext λ _ → U[])) (appNI (tr (Tm _) ΠNI[] vz) a)) a))

Eq'' : (A : Set) → Con
Eq'' A = ∙
  ▶ ΠNI (A × A) (λ _ → U)
  ▶ ΠNI A (λ a → El (appNI zNU (a , a)))

W : (A : Set) → (A → Set) → Con
W S P = ∙
  ▶ U
  ▶ ΠNI S (λ s → Π (Πₙᵢ (P s) (λ _ → zU)) (El (sU zU)))

propTrunc : Set → Con
propTrunc A = ∙
  ▶ U
  ▶ ΠNI A (λ _ → El zU)
  ▶ Π (sU zU) (Π (sU sU zU) (El (Id _ (sEl zEl) zEl)))

setTrunc' : Set → Con
setTrunc' A = ∙
  ▶ U
  ▶ ΠNI A (λ _ → El zU)
  ▶ Π (sU zU)
     (Π (sU sU zU)
       (Π (Id _ (sEl zEl) zEl)
         (Π (Id _ (sEl sEl zEl) (sEl zEl))
           (El (Id _ (sId zId) zId)))))

-- Inductive-inductive Con-Ty-Tm-Sub sorts of type theory syntax
TTSorts : Con
TTSorts = ∙
  ▶ U
  ▶ Π zU U
  ▶ Π (sU zU) (Π (sU sU zU) U)
  ▶ Π (sU sU zU) (Π ((sΠU sΠU zΠU) $U zEl) U)
