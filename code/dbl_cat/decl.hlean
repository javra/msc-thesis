import algebra.category.basic

open precategory morphism truncation eq sigma sigma.ops

-- HERE BE DRAGONS
structure worm_precat {D₀ : Type} (C : precategory D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) : Type :=
  (comp₁ : Π {a b c₁ d₁ c₂ d₂ : D₀} ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄
    ⦃i₁ : hom b d₁⦄ ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄,
    (D₂ g₁ g₂ h₂ i₂) → (D₂ f₁ g₁ h₁ i₁) → (@D₂ a b c₂ d₂ f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁)))
  (ID₁ : Π {a b : D₀} (f : hom a b), D₂ f f (ID a) (ID b))
  (assoc₁ : Π {a b c₁ d₁ c₂ d₂ c₃ d₃ : D₀}
    {f : hom a b} {g₁ : hom c₁ d₁} {h₁ : hom a c₁} {i₁ : hom b d₁}
    {g₂ : hom c₂ d₂} {h₂ : hom c₁ c₂} {i₂ : hom d₁ d₂}
    {g₃ : hom c₃ d₃} {h₃ : hom c₂ c₃} {i₃ : hom d₂ d₃}
    (w : D₂ g₂ g₃ h₃ i₃) (v : D₂ g₁ g₂ h₂ i₂) (u : D₂ f g₁ h₁ i₁),
    transport (λ x, D₂ f g₃ _ x) (assoc i₃ i₂ i₁)
      (transport (λ x, D₂ f g₃ x _) (assoc h₃ h₂ h₁)
        (comp₁ w (comp₁ v u))) = (comp₁ (comp₁ w v) u))
  (id_left₁ : Π {a b c d : D₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    transport (λ x, D₂ f g h x) (id_left i)
      (transport (λ x, D₂ f g x _) (id_left h)
        (comp₁ (ID₁ g) u)) = u)
  (id_right₁ : Π {a b c d : D₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    transport (λ x, D₂ f g h x) (id_right i)
      (transport (λ x, D₂ f g x _) (id_right h)
        (comp₁  u (ID₁ f))) = u)

structure dbl_precat [class] {D₀ : Type} (C : precategory D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type)
  extends worm_precat C D₂,
    worm_precat C (λ ⦃a b c d : D₀⦄ f g h i, D₂ h i f g)
      renaming comp₁→comp₂ ID₁→ID₂ assoc₁→assoc₂
        id_left₁→id_left₂ id_right₁→id_right₂ :=
  (homH' : Π {a b c d : D₀} {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    is_hset (D₂ f g h i))
  (interchange : Π {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : D₀}
    {f₀₀ : hom a₀₀ a₀₁} {f₀₁ : hom a₀₁ a₀₂} {f₁₀ : hom a₁₀ a₁₁}
    {f₁₁ : hom a₁₁ a₁₂} {f₂₀ : hom a₂₀ a₂₁} {f₂₁ : hom a₂₁ a₂₂}
    {g₀₀ : hom a₀₀ a₁₀} {g₀₁ : hom a₀₁ a₁₁} {g₀₂ : hom a₀₂ a₁₂}
    {g₁₀ : hom a₁₀ a₂₀} {g₁₁ : hom a₁₁ a₂₁} {g₁₂ : hom a₁₂ a₂₂}
    (x : D₂ f₁₁ f₂₁ g₁₁ g₁₂) (w : D₂ f₁₀ f₂₀ g₁₀ g₁₁)
    (v : D₂ f₀₁ f₁₁ g₀₁ g₀₂) (u : D₂ f₀₀ f₁₀ g₀₀ g₀₁),
    comp₁ (comp₂ x w) (comp₂ v u) = comp₂ (comp₁ x v) (comp₁ w u))


inductive Dbl_precat : Type :=
mk : Π {D₀ : Type} [C : precategory D₀]
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b)
    (g : hom c d) (h : hom a c) (i : hom b d), Type),
  dbl_precat C D₂ → Dbl_precat

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : dbl_precat C D₂]
  include C D

  definition D₁ : D₀ → D₀ → Type := @hom D₀ C

  /-set_option pp.universes true
  set_option pp.implicit true
  definition vert_precat : precategory (Σ (a b : D₀), hom a b) :=
  begin
    fapply precategory.mk,
                intros (S, T),
                exact (Σ (h : hom S.1 T.1) (i : hom S.2.1 T.2.1), D₂ S.2.2 T.2.2 h i),
              intros, apply trunc_sigma, apply !homH,
              intro f, apply trunc_sigma, apply !homH,
              intro g, apply !homH',
            intros (S, T, U, V, W), fapply sigma.mk, apply (comp (V.1) (W.1)),
            fapply sigma.mk, apply (@comp D₀ C S.2.1 T.2.1 U.2.1 (V.2.1) (W.2.1)),
            exact (@comp₁ D₀ C D₂ D S.1 S.2.1 T.1 T.2.1 _ _ _ _ _ _ _ _ _ (V.2.2) (W.2.2)),
  end-/

  variables {a b c d a₂ b₂ c₂ d₂ d₃ d₄ : D₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {f₂ : hom b b₂} {g₂ : hom d d₂} {i₂ : hom b₂ d₂}
    {g₃ : hom c₂ d₃} {h₂ : hom c c₂} {i₃ : hom d d₃}
    (u : D₂ f g h i)
    (v : D₂ f₂ g₂ i i₂)
    (w : D₂ g g₃ h₂ i₃)

  notation u `+₁` v := comp₁ v u
  notation u `+₂` v := comp₂ v u

  definition bnd_upper (u : D₂ f g h i) := f
  definition bnd_lower (u : D₂ f g h i) := g
  definition bnd_left (u : D₂ f g h i) := h
  definition bnd_right (u : D₂ f g h i) := i

  notation `∂₁⁻` u := bnd_upper u
  notation `∂₁⁺` u := bnd_lower u
  notation `∂₂⁻` u := bnd_left u
  notation `∂₂⁺` u := bnd_right u

  notation `ε₁` f := ID₁ f
  notation `ε₂` f := ID₂ f

  definition zero (a : D₀) : D₂ (ID a) (ID a) (ID a) (ID a) := (@ID₁ D₀ C D₂ D a a (ID a))
  notation `◻` := zero

  check @bnd_left
  definition DC4_1 (u : D₂ f g h i) (v : D₂ f₂ g₂ i i₂)
    : (@bnd_left D₀ C D₂ D _ _ _ _ _ _ _ _ (@comp₁ D₀ C D₂ D a b c d c₂ d₃ f g h i g₃ h₂ i₃ w u)) = (bnd_left w) ∘ (bnd_left u) := idp

  check DC4_1

end dbl_precat
