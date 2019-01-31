-- Agda header
U = Set

infix 4 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
  refl : x ≡ x

J : ∀{α β}{A : Set α} {a₀ : A} (P : (a₁ : A) → a₀ ≡ a₁ → Set β) → P _ refl → ∀ {a₁}(p : a₀ ≡ a₁) → P a₁ p
J P pr refl = pr

tr : ∀{α β}{A : Set α}(B : A → Set β){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B eq t = J (λ x _ → B x) t eq

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
  surfᴱ : tr (λ u' → tr (λ u'' → tr S²ᴹ u'' baseᴹ ≡ baseᴹ) surf u' ≡ refl) (J (λ xᴹ' xᴱ' → tr (λ u' → u' ≡ xᴹ') xᴱ' (tr (λ u' → S²ᴱ base ≡ u') xᴱ' refl) ≡ refl) refl baseᴱ) (tr (λ u' → tr (λ u'' → tr S²ᴹ u'' baseᴹ ≡ baseᴹ) surf (tr (λ u'' → u'' ≡ baseᴹ) baseᴱ (tr (λ u'' → S²ᴱ base ≡ u'') baseᴱ refl)) ≡ u') (J (λ xᴹ' xᴱ' → tr (λ u' → u' ≡ xᴹ') xᴱ' (tr (λ u' → S²ᴱ base ≡ u') xᴱ' refl) ≡ refl) refl baseᴱ) (J (λ u' p' → tr (λ u'' → tr S²ᴹ u'' baseᴹ ≡ baseᴹ) p' (tr (λ u'' → u'' ≡ baseᴹ) baseᴱ (tr (λ u'' → S²ᴱ base ≡ u'') baseᴱ refl)) ≡ tr (λ u'' → tr S²ᴹ u' u'' ≡ baseᴹ) baseᴱ (tr (λ u'' → tr S²ᴹ u' (S²ᴱ base) ≡ u'') baseᴱ (J (λ u'' p'' → tr S²ᴹ p'' (S²ᴱ base) ≡ S²ᴱ u'') refl u'))) refl surf)) ≡ surfᴹ
