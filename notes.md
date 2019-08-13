
ID model

(Γ : Con)ᴵ     : (γ : Γᴬ) → Γᴹ γ γ
(A : Ty Γ)ᴵ    : (γ : Γᴬ)(t : Aᴬ γ) → Aᴹ γ γ (Γᴵ γ) t t
(σ : Sub Γ Δ)ᴵ : ∀ γ. σᴹ γ γ (Γᴵ γ) ≡ Δᴵ (σᴬ γ)
(t : Tm Γ A)ᴵ  : ∀ γ. tᴹ γ γ (Γᴵ γ) ≡ Aᴵ γ (tᴬ γ)

∙ᴵ       γ      := tt
(Γ ▶ A)ⁱ (γ, α) := (Γᴵ γ, Aᴵ γ α)

(A[σ : Sub Γ Δ])ᴵ (γ : Γᴬ)(t : Aᴬ (σᴬ γ))
  : (A[σ])ᴹ γ γ (Γᴵ γ) t t
  : Aᴹ (σᴬ γ) (σᴬ γ) (σᴹ (Γⁱ γ)) t t

  (A[σ])ᴵ γ t := Aᴵ (σᴬ γ) t

Uᴵ γ (t : Set) : t → t
  Uᴵ γ t := λ x. x

U[] : (U[σ])ᴵ ≡ Uᴵ
    : (λ γ t. Uᴵ (σᴬ γ) t) ≡ (λ γ t. Uᴵ γ t)
	: (λ x. x) ≡ (λ x. x) OK

(El a)ᴵ γ (t : aᴬ γ)
  : (El a)ᴹ γ γ (Γᴵ γ) t t
  : aᴹ (Γᴵ γ) t = t

  aᴵ γ : aᴹ _ _ (Γᴵ γ) ≡ Uᴵ γ (tᴬ γ)
       : aᴹ (Γᴵ γ) ≡ λ x. x
    hence, aᴹ (Γᴵ γ) t ≡ t

  (El a)ᴵ γ t := refl

(Π a B)ᴵ γ (t : (x : aᴬ γ) → Bᴬ (γ, x))
  : (Π a B)ᴹ γ γ (Γᴵ γ) t t
  : (x : aᴬ γ) → Bᴹ (γ, x) (γ, aᴹ (Γᴵ γ) x) (Γᴵ γ, refl) (t x) (t (aᴹ (Γᴵ γ) x))
  : (x : aᴬ γ) → Bᴹ (γ, x) (γ, x) (Γᴵ γ, refl) (t x) (t x)
  := λ x. Bᴵ (γ, x) (t x)

(app t u)ᴵ γ
  : (app t u)ᴹ γ γ (Γᴵ γ) ≡ (B[id, u])ᴵ γ ((app t u)ᴬ γ)
  : J (tᴹ (Γᴵ γ) (uᴬ γ)) (uᴹ (Γᴵ γ)) ≡ Bᴵ (γ, uᴬ γ) (tᴬ γ (uᴬ γ))

  u : Tm Γ (El a)
  uᴵ γ : uᴹ (Γᴵ γ) ≡ (El a)ᴵ γ (uᴬ γ)
       : uᴹ (Γᴵ γ) ≡ refl

  hence enough to show
  : tᴹ (Γᴵ γ) (uᴬ γ) ≡ Bᴵ (γ, uᴬ γ) (tᴬ γ (uᴬ γ))

  tᴵ γ : tᴹ (Γᴵ γ) ≡ (Π a B)ᴵ γ (tᴬ γ)
       : tᴹ (Γᴵ γ) ≡ (λ x. Bᴵ (γ, x) (tᴬ γ x))
    hence tᴹ (Γᴵ γ) (uᴬ γ) ≡ Bᴵ (γ, x) (tᴬ γ (uᴬ γ)))

  OK

(t =ₐ u)ᴵ γ
  : (t = u)ᴹ γ γ (Γᴵ γ) ≡ Uᴵ γ (tᴬ γ)
  : (t = u)ᴹ γ γ (Γᴵ γ) ≡ λ x. x
  : (λ e. (tᴹ (Γᴵ γ))⁻¹ ◾ ap (aᴹ (Γᴵ γ)) e ◾ uᴹ (Γᴵ γ)) ≡ (λ x. x)
  : (λ e. refl ◾ ap (λ x. x) e ◾ refl) ≡ (λ e. e)
  DOESN'T WORK

  What happens in 2lvl-tt? It works if we have (ap id e = e) and
  refl ◾ e = e as strict equalities whenever e if fibrant equality.
  I'm not familiar enough with 2lvl-tt to know this.

reflᴵ γ :
