{-# OPTIONS --without-K #-}

module Lib where

open import Agda.Builtin.Equality public
open import Agda.Primitive public

record Lift {a} {ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

ap : ∀ {α β}{A : Set α}{B : Set β}(f : A → B){x y} → x ≡ y → f x ≡ f y
ap f refl = refl

tr : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B refl b₀ = b₀

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
infixr 5 _,_

Σ,= : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → tr B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
Σ,= refl refl = refl

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B
infixr 4 _×_



-- function extensionality
postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

happly : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a} → f ≡ g → ∀ a → f a ≡ g a
happly p a = ap (λ f → f a) p

happlyi : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ {a} → B a} → (λ {x} → f {x}) ≡ g → ∀ a → f {a} ≡ g {a}
happlyi p a = ap (λ f → f {a}) p

isEquiv : ∀{i j}{A : Set i}{B : Set j}(f : A → B) → Set _
isEquiv {A = A}{B} f =
  ∃₂ λ (g h : B → A) → (∀ b → f (g b) ≡ b) × (∀ b → g (f b) ≡ b)

trᴹ :
  ∀ {i j k l}
    {A  : Set i}    {Aᴹ : A → Set j}
    {B  : A → Set k}(Bᴹ : ∀ {a} → Aᴹ a → B a → Set l)
    {a₀ : A}        {a₀ᴹ : Aᴹ a₀}
    {a₁ : A}        {a₁ᴹ : Aᴹ a₁}
    (a₂ : a₀ ≡ a₁)  (a₂ᴹ : tr Aᴹ a₂ a₀ᴹ ≡ a₁ᴹ)
    {b₀ : B a₀}
    {b₁ : B a₁}
    (b₂ : tr B a₂ b₀ ≡ b₁)
  → Bᴹ a₀ᴹ b₀ → Bᴹ a₁ᴹ b₁
trᴹ Bᴹ refl refl refl b₀ᴹ = b₀ᴹ

tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀}{.a₀} refl refl c₀ = c₀

tr2ᴹ :
  ∀ {i j k l m n}
    {A  : Set i}            {Aᴹ : A → Set l}
    {B  : A → Set j}        {Bᴹ : ∀ {a} → Aᴹ a → B a → Set m}
    {C  : ∀ a → B a → Set k}(Cᴹ : ∀ {a} (aᴹ : Aᴹ a) {b} (bᴹ : Bᴹ aᴹ b) → C a b → Set n)
    {a₀ : A}                {a₀ᴹ : Aᴹ a₀}
    {a₁ : A}                {a₁ᴹ : Aᴹ a₁}
    (a₂ : a₀ ≡ a₁)          (a₂ᴹ : tr Aᴹ a₂ a₀ᴹ ≡ a₁ᴹ)
    {b₀ : B a₀}             {b₀ᴹ : Bᴹ a₀ᴹ b₀}
    {b₁ : B a₁}             {b₁ᴹ : Bᴹ a₁ᴹ b₁}
    (b₂ : tr B a₂ b₀ ≡ b₁)  (b₂ᴹ : trᴹ Bᴹ a₂ a₂ᴹ b₂ b₀ᴹ ≡ b₁ᴹ)
    {c₀ : C a₀ b₀} {c₁ : C a₁ b₁}(c₂ : tr2 C a₂ b₂ c₀ ≡ c₁)
  → Cᴹ a₀ᴹ b₀ᴹ c₀ → Cᴹ a₁ᴹ b₁ᴹ c₁
tr2ᴹ Cᴹ {a₀ᴹ = a₀ᴹ} refl refl refl refl refl c₀ᴹ = c₀ᴹ

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ q = q
infixr 4 _◾_

tr-tr : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}{a₂ : A}
        (a₀₁ : a₀ ≡ a₁)(a₁₂ : a₁ ≡ a₂){b₀ : B a₀}
      → tr B a₁₂ (tr B a₀₁ b₀) ≡ tr B (a₀₁ ◾ a₁₂) b₀
tr-tr B refl refl = refl

◾refl : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (p ◾ refl) ≡ p
◾refl refl = refl

refl◾ : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (refl ◾ p) ≡ p
refl◾ refl = refl

_⁻¹ : ∀{i}{A : Set i}{a₀ a₁ : A} → a₀ ≡ a₁ → a₁ ≡ a₀
refl ⁻¹ = refl
infix 6 _⁻¹

inv : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → ((p ⁻¹) ◾ p) ≡ refl
inv refl = refl

tr⁻¹ : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
       {b₀ : B a₀}{b₁ : B a₁}
     → tr B (a₂ ⁻¹) b₁ ≡ b₀ → b₁ ≡ tr B a₂ b₀
tr⁻¹ B refl p = p

⁻¹ᴹ :
  ∀ {j}
    {A : Set}(Aᴹ : A → Set j)
    {t : A}{tᴹ : Aᴹ t}
    {u : A}{uᴹ : Aᴹ u}
    (p : t ≡ u)(pᴹ : tr Aᴹ p tᴹ ≡ uᴹ)
    → tr Aᴹ (p ⁻¹) uᴹ ≡ tᴹ
⁻¹ᴹ {j} {A} Aᴹ {t} {tᴹ} {.t} {.tᴹ} refl refl = refl

ap-id : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → ap (λ x → x) p ≡ p
ap-id refl = refl

ap-const : ∀ {α β}{A : Set α}{B : Set β}(b : B){x y : A}(p : x ≡ y) → ap (λ _ → b) p ≡ refl
ap-const b refl = refl

ap-◾ : ∀ {α β}{A : Set α}{B : Set β}(f : A → B){x y z : A}(p : x ≡ y)(q : y ≡ z) → (ap f (p ◾ q)) ≡ (ap f p ◾ ap f q)
ap-◾ f refl refl = refl

tr-ap : ∀ {i j}{A A' : Set i}(B : A' → Set j)(f : A → A')
       {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B (f a₀)}
     → tr (λ z → B (f z)) a₂ b₀ ≡ tr B (ap f a₂) b₀
tr-ap B f refl = refl

apd : ∀ {α β}{A : Set α}{B : A → Set β}(f : (x : A) → B x){x y}(p : x ≡ y) → tr B p (f x) ≡ f y
apd f refl = refl

ap2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}{C : Set k}(f : ∀ a → B a → C)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl = refl

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x

J :
  ∀{α β}{A : Set α} {x : A} (P : (y : A) → x ≡ y → Set β)
  → P _ refl → {y : A} → (w : x ≡ y) → P _ w
J P pr refl = pr

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀{i}{A : Set i} → ⊥ → A
⊥-elim ()
