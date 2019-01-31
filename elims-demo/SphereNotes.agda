{-# OPTIONS --rewriting #-}

{- The surfᴱ type below is computed by an alternative _ᴱ definition for _≡_ and refl,
   which uses _◾_, _⁻¹, ap, apd, inv, ap-id and tr-◾.
   The implementation is the following (in shallow style)

   ≡ᴱ :
     (a : U)(aᴹ : Uᴹ a)    (aᴱ : Uᴱ a aᴹ)
     (t : a)(tᴹ : Elᴹ aᴹ t)(tᴱ : Elᴱ _ aᴹ aᴱ t tᴹ)
     (u : a)(uᴹ : Elᴹ aᴹ u)(uᴱ : Elᴱ _ aᴹ aᴱ u uᴹ)
     → Uᴱ (t ≡ u) (≡ᴹ aᴹ tᴹ uᴹ)
   ≡ᴱ a aᴹ aᴱ t tᴹ tᴱ u uᴹ uᴱ =
     λ e → ap (tr aᴹ e) (tᴱ ⁻¹) ◾ apd aᴹ aᴱ t u e ◾ uᴱ

   reflᴱ :
     {a : U} (aᴹ : Uᴹ a)    (aᴱ : Uᴱ a aᴹ)
     {t : a} (tᴹ : Elᴹ aᴹ t)(tᴱ : Elᴱ _ aᴹ aᴱ t tᴹ)
     → Elᴱ _ (≡ᴹ aᴹ tᴹ tᴹ) (≡ᴱ a aᴹ aᴱ t tᴹ tᴱ t tᴹ tᴱ) refl (reflᴹ aᴹ tᴹ)
   reflᴱ {a} aᴹ aᴱ {t} tᴹ tᴱ =
     ap (_◾ tᴱ) (ap-id (tᴱ ⁻¹)) ◾ inv tᴱ
-}

-- Agda header
U = Set

infix 4 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

J : ∀{α β}{A : Set α} {a₀ : A} (P : (a₁ : A) → a₀ ≡ a₁ → Set β) → P _ refl → ∀ {a₁}(p : a₀ ≡ a₁) → P a₁ p
J P pr refl = pr

tr : ∀{α β}{A : Set α}(B : A → Set β){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B eq t = J (λ x _ → B x) t eq

ap : ∀ {α β}{A : Set α}{B : Set β}(f : A → B){x y : A}(p : x ≡ y) → f x ≡ f y
ap {A = A} {B} f {x} {y} p = tr (λ y → f x ≡ f y) p refl

apd : ∀ {α β}{A : Set α}{B : A → Set β}(f : ∀ a → B a){x y : A}(p : x ≡ y) → tr B p (f x) ≡ f y
apd {A = A} {B} f {t} {u} p = J (λ y p → tr B p (f t) ≡ f y) (refl {x = f t}) p

infixl 5 _◾_
_◾_ : ∀ {α}{A : Set α}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◾_ {x = x}{y}{z} p q = tr (λ z → x ≡ z) q p

infix 6 _⁻¹
_⁻¹ : ∀ {α}{A : Set α}{x y : A} → x ≡ y → y ≡ x
_⁻¹ {A = A} {x} {y} p = tr (λ z → z ≡ x) p refl

ap-id : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → ap (λ x → x) p ≡ p
ap-id refl = refl

inv : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (p ⁻¹) ◾ p ≡ refl
inv refl = refl

postulate
  -- Constructors:
  S² : U
  base : S²
  surf : refl {x = base} ≡ refl

  -- Induction methods:
  S²ᴹ : S² → U
  baseᴹ : S²ᴹ base
  surfᴹ : tr (λ u' → tr S²ᴹ u' baseᴹ ≡ baseᴹ) surf refl ≡ refl

  -- Eliminators and β-rules:
  S²ᴱ : (x' : S²) → S²ᴹ x'
  baseᴱ : S²ᴱ base ≡ baseᴹ

postulate
  -- structured version from alternative Idᴱ and reflᴱ
  surfᴱ :
    let reflᴱ = ap (_◾ baseᴱ) (ap-id (baseᴱ ⁻¹)) ◾ inv baseᴱ in

      ap (tr (λ e → tr S²ᴹ e baseᴹ ≡ baseᴹ) surf) (reflᴱ ⁻¹)
    ◾ apd (λ e → ap (tr S²ᴹ e) (baseᴱ ⁻¹) ◾ apd S²ᴱ e ◾ baseᴱ) surf
    ◾ reflᴱ
    ≡ surfᴹ

-- version with more REWRITing
{-# REWRITE baseᴱ #-}
postulate
  baseᴱrefl : baseᴱ ≡ refl
{-# REWRITE baseᴱrefl #-}
postulate
  surfᴱ' :
      apd (apd S²ᴱ) surf ≡ surfᴹ
