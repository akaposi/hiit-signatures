
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
  -- External context:
  Q : U
  plus : Q → Q → Q
  neg : Q → Q
  lt : Q → Q → U

  -- Algebras
  R : U
  Rel : Q → R → R → U
  rat : Q → R
  lim : (seq : Q → R) → ((δ : Q)(ε : Q) → Rel (plus δ ε) (seq δ) (seq ε)) → R
  eqR : (u : R)(v : R) → ((ε : Q) → Rel ε u v) → u ≡ v
  ratRat : (q : Q)(r : Q)(ε : Q) → lt (neg ε) (plus q (neg r)) → lt (plus q (neg r)) ε → Rel ε (rat q) (rat r)
  ratLim : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁)) → Rel (plus ε (neg δ)) (rat q) (y δ) → Rel ε (rat q) (lim y py)
  limRat : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁)) → Rel (plus ε (neg δ)) (y δ) (rat q) → Rel ε (lim y py) (rat q)
  limLim : (ε : Q)(δ : Q)(η : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(x : Q → R)(px : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (x δ₁) (x ε₁)) → Rel (plus ε (plus (neg δ) (neg η))) (x δ) (y η) → Rel ε (lim x px) (lim y py)
  trunc : (u : R)(v : R)(ε : Q)(p : Rel ε u v)(q : Rel ε u v) → p ≡ q

  -- Displayed algebras
  Rᴰ : R → U
  Relᴰ : (q : Q)(r : R) → Rᴰ r → (r1 : R) → Rᴰ r1 → Rel q r r1 → U
  ratᴰ : (q : Q) → Rᴰ (rat q)
  limᴰ : (seq : Q → R)(seqᴰ : (q : Q) → Rᴰ (seq q))(f : (δ : Q)(ε : Q) → Rel (plus δ ε) (seq δ) (seq ε)) → ((δ : Q)(ε : Q) → Relᴰ (plus δ ε) (seq δ) (seqᴰ δ) (seq ε) (seqᴰ ε) (f δ ε)) → Rᴰ (lim seq f)
  eqRᴰ : (u : R)(uᴰ : Rᴰ u)(v : R)(vᴰ : Rᴰ v)(f : (ε : Q) → Rel ε u v) → ((ε : Q) → Relᴰ ε u uᴰ v vᴰ (f ε)) → tr Rᴰ (eqR u v f) uᴰ ≡ vᴰ
  ratRatᴰ : (q : Q)(r : Q)(ε : Q)(l : lt (neg ε) (plus q (neg r)))(l1 : lt (plus q (neg r)) ε) → Relᴰ ε (rat q) (ratᴰ q) (rat r) (ratᴰ r) (ratRat q r ε l l1)
  ratLimᴰ : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(yᴰ : (q1 : Q) → Rᴰ (y q1))(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(pyᴰ : (δ₁ : Q)(ε₁ : Q) → Relᴰ (plus δ₁ ε₁) (y δ₁) (yᴰ δ₁) (y ε₁) (yᴰ ε₁) (py δ₁ ε₁))(r : Rel (plus ε (neg δ)) (rat q) (y δ)) → Relᴰ (plus ε (neg δ)) (rat q) (ratᴰ q) (y δ) (yᴰ δ) r → Relᴰ ε (rat q) (ratᴰ q) (lim y py) (limᴰ y yᴰ py pyᴰ) (ratLim q ε δ y py r)
  limRatᴰ : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(yᴰ : (q1 : Q) → Rᴰ (y q1))(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(pyᴰ : (δ₁ : Q)(ε₁ : Q) → Relᴰ (plus δ₁ ε₁) (y δ₁) (yᴰ δ₁) (y ε₁) (yᴰ ε₁) (py δ₁ ε₁))(r : Rel (plus ε (neg δ)) (y δ) (rat q)) → Relᴰ (plus ε (neg δ)) (y δ) (yᴰ δ) (rat q) (ratᴰ q) r → Relᴰ ε (lim y py) (limᴰ y yᴰ py pyᴰ) (rat q) (ratᴰ q) (limRat q ε δ y py r)
  limLimᴰ : (ε : Q)(δ : Q)(η : Q)(y : Q → R)(yᴰ : (q : Q) → Rᴰ (y q))(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(pyᴰ : (δ₁ : Q)(ε₁ : Q) → Relᴰ (plus δ₁ ε₁) (y δ₁) (yᴰ δ₁) (y ε₁) (yᴰ ε₁) (py δ₁ ε₁))(x : Q → R)(xᴰ : (q : Q) → Rᴰ (x q))(px : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (x δ₁) (x ε₁))(pxᴰ : (δ₁ : Q)(ε₁ : Q) → Relᴰ (plus δ₁ ε₁) (x δ₁) (xᴰ δ₁) (x ε₁) (xᴰ ε₁) (px δ₁ ε₁))(r : Rel (plus ε (plus (neg δ) (neg η))) (x δ) (y η)) → Relᴰ (plus ε (plus (neg δ) (neg η))) (x δ) (xᴰ δ) (y η) (yᴰ η) r → Relᴰ ε (lim x px) (limᴰ x xᴰ px pxᴰ) (lim y py) (limᴰ y yᴰ py pyᴰ) (limLim ε δ η y py x px r)
  truncᴰ : (u : R)(uᴰ : Rᴰ u)(v : R)(vᴰ : Rᴰ v)(ε : Q)(p : Rel ε u v)(pᴰ : Relᴰ ε u uᴰ v vᴰ p)(q : Rel ε u v)(qᴰ : Relᴰ ε u uᴰ v vᴰ q) → tr (Relᴰ ε u uᴰ v vᴰ) (trunc u v ε p q) pᴰ ≡ qᴰ

  -- Displayed algebra sections
  Rˢ : (x' : R) → Rᴰ x'
  Relˢ : (q : Q)(r : R)(r1 : R)(x' : Rel q r r1) → Relᴰ q r (Rˢ r) r1 (Rˢ r1) x'
  ratˢ : (q : Q) → Rˢ (rat q) ≡ ratᴰ q
  limˢ : (seq : Q → R)(f : (δ : Q)(ε : Q) → Rel (plus δ ε) (seq δ) (seq ε)) → Rˢ (lim seq f) ≡ limᴰ seq (λ q → Rˢ (seq q)) f (λ δ ε → Relˢ (plus δ ε) (seq δ) (seq ε) (f δ ε))
  eqRˢ : (u : R)(v : R)(f : (ε : Q) → Rel ε u v) → apd Rˢ (eqR u v f) ≡ eqRᴰ u (Rˢ u) v (Rˢ v) f (λ ε → Relˢ ε u v (f ε))
  ratRatˢ : (q : Q)(r : Q)(ε : Q)(l : lt (neg ε) (plus q (neg r)))(l1 : lt (plus q (neg r)) ε) → (tr (λ uᴹ' → (x' : Rel ε (rat q) (rat r)) → Relᴰ ε (rat q) (ratᴰ q) (rat r) uᴹ' x') (ratˢ r) ((tr (λ uᴹ' → (r11 : R)(x' : Rel ε (rat q) r11) → Relᴰ ε (rat q) uᴹ' r11 (Rˢ r11) x') (ratˢ q) (Relˢ ε (rat q))) (rat r))) (ratRat q r ε l l1) ≡ ratRatᴰ q r ε l l1
  ratLimˢ : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(r : Rel (plus ε (neg δ)) (rat q) (y δ)) → (tr (λ uᴹ' → (x' : Rel ε (rat q) (lim y py)) → Relᴰ ε (rat q) (ratᴰ q) (lim y py) uᴹ' x') (limˢ y py) ((tr (λ uᴹ' → (r11 : R)(x' : Rel ε (rat q) r11) → Relᴰ ε (rat q) uᴹ' r11 (Rˢ r11) x') (ratˢ q) (Relˢ ε (rat q))) (lim y py))) (ratLim q ε δ y py r) ≡ ratLimᴰ q ε δ y (λ q1 → Rˢ (y q1)) py (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (y δ₁) (y ε₁) (py δ₁ ε₁)) r (tr (λ uᴹ' → (r1 : R)(x' : Rel (plus ε (neg δ)) (rat q) r1) → Relᴰ (plus ε (neg δ)) (rat q) uᴹ' r1 (Rˢ r1) x') (ratˢ q) (Relˢ (plus ε (neg δ)) (rat q)) (y δ) r)
  limRatˢ : (q : Q)(ε : Q)(δ : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(r : Rel (plus ε (neg δ)) (y δ) (rat q)) → (tr (λ uᴹ' → (x' : Rel ε (lim y py) (rat q)) → Relᴰ ε (lim y py) (limᴰ y (λ q1 → Rˢ (y q1)) py (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (y δ₁) (y ε₁) (py δ₁ ε₁))) (rat q) uᴹ' x') (ratˢ q) ((tr (λ uᴹ' → (r11 : R)(x' : Rel ε (lim y py) r11) → Relᴰ ε (lim y py) uᴹ' r11 (Rˢ r11) x') (limˢ y py) (Relˢ ε (lim y py))) (rat q))) (limRat q ε δ y py r) ≡ limRatᴰ q ε δ y (λ q1 → Rˢ (y q1)) py (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (y δ₁) (y ε₁) (py δ₁ ε₁)) r ((tr (λ uᴹ' → (x' : Rel (plus ε (neg δ)) (y δ) (rat q)) → Relᴰ (plus ε (neg δ)) (y δ) (Rˢ (y δ)) (rat q) uᴹ' x') (ratˢ q) (Relˢ (plus ε (neg δ)) (y δ) (rat q))) r)
  limLimˢ : (ε : Q)(δ : Q)(η : Q)(y : Q → R)(py : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (y δ₁) (y ε₁))(x : Q → R)(px : (δ₁ : Q)(ε₁ : Q) → Rel (plus δ₁ ε₁) (x δ₁) (x ε₁))(r : Rel (plus ε (plus (neg δ) (neg η))) (x δ) (y η)) → (tr (λ uᴹ' → (x' : Rel ε (lim x px) (lim y py)) → Relᴰ ε (lim x px) (limᴰ x (λ q → Rˢ (x q)) px (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (x δ₁) (x ε₁) (px δ₁ ε₁))) (lim y py) uᴹ' x') (limˢ y py) ((tr (λ uᴹ' → (r11 : R)(x' : Rel ε (lim x px) r11) → Relᴰ ε (lim x px) uᴹ' r11 (Rˢ r11) x') (limˢ x px) (Relˢ ε (lim x px))) (lim y py))) (limLim ε δ η y py x px r) ≡ limLimᴰ ε δ η y (λ q → Rˢ (y q)) py (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (y δ₁) (y ε₁) (py δ₁ ε₁)) x (λ q → Rˢ (x q)) px (λ δ₁ ε₁ → Relˢ (plus δ₁ ε₁) (x δ₁) (x ε₁) (px δ₁ ε₁)) r (Relˢ (plus ε (plus (neg δ) (neg η))) (x δ) (y η) r)
  truncˢ : (u : R)(v : R)(ε : Q)(p : Rel ε u v)(q : Rel ε u v) → apd (Relˢ ε u v) (trunc u v ε p q) ≡ truncᴰ u (Rˢ u) v (Rˢ v) ε p (Relˢ ε u v p) q (Relˢ ε u v q)
