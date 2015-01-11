import types.sigma
import .decl

open precategory morphism truncation eq sigma sigma.ops unit nat

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
  include C

  definition square_dbl_precat : dbl_precat
    (λ ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), unit) :=
  begin
    fapply dbl_precat.mk,
    repeat ( intros ;
      [ exact ⋆ |
        [ apply (@is_hprop.elim) | apply trunc_succ ] ;
        apply trunc_succ ; exact unit_contr ] ),
    repeat ( intros;  apply idp)
  end

  definition comm_square_dbl_precat : dbl_precat
    (λ ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), g ∘ h = i ∘ f) :=
  begin
    fapply dbl_precat.mk,
      intros, exact (calc g₂ ∘ h₂ ∘ h₁ = (g₂ ∘ h₂) ∘ h₁ : assoc
                                  ... = (i₂ ∘ g₁) ∘ h₁ : a_1
                                  ... = i₂ ∘ g₁ ∘ h₁ : assoc
                                  ... = i₂ ∘ i₁ ∘ f₁ : a_2
                                  ... = (i₂ ∘ i₁) ∘ f₁ : assoc),
      intros, exact (calc f ∘ ID a = f : id_right
                               ... = ID b ∘ f : id_left),
      repeat ( intros ; apply @is_hset.elim ; apply !homH ),
      intros,  exact (calc (i₂ ∘ i₁) ∘ f₁ = i₂ ∘ i₁ ∘ f₁ : assoc
                                     ... = i₂ ∘ g₁ ∘ h₁ : a_2
                                     ... = (i₂ ∘ g₁) ∘ h₁ : assoc
                                     ... = (g₂ ∘ h₂) ∘ h₁ : a_1
                                     ... = g₂ ∘ h₂ ∘ h₁ : assoc),
      intros, exact (calc ID b ∘ f = f : id_left
                               ... = f ∘ ID a : id_right),
      repeat ( intros ; apply @is_hset.elim ; apply !homH ),
      intros, apply succ_is_trunc, apply trunc_succ, apply !homH,
      repeat ( intros ; apply @is_hprop.elim ;  apply succ_is_trunc ;  apply !homH ),
  end

end dbl_precat

check @dbl_precat.comp₁

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : @dbl_precat D₀ C D₂]
  include C D

  variables {a b c d a₂ b₂ c₂ d₂ d₃ d₄ : D₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {f₂ : hom b b₂} {g₂ : hom d d₂} {i₂ : hom b₂ d₂}
    {g₃ : hom c₂ d₃} {h₂ : hom c c₂} {i₃ : hom d d₃}
    (u : D₂ f g h i)
    (v : D₂ f₂ g₂ i i₂)
    (w : D₂ g g₃ h₂ i₃)

  notation u `+₁` v := comp₁ v u
  notation u `+₂` v := comp₂ v u

end dbl_precat

namespace dbl_precat
  universe variables l₀ l₁ l₂
  /-variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}
    [D : dbl_precat D₂]-/
  variables {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : dbl_precat D₂]
  include C D

  definition D₁ : D₀ → D₀ → Type := @hom D₀ C


  set_option pp.compact_goals true
  set_option pp.beta true
  definition vert_connect {a b c d : D₀} (f : hom a b) (g : hom c d) :=
  Σ (h : hom a c) (i : hom b d), D₂ f g h i

  check assoc
  definition vert_comp {a₁ a₂ a₃ b₁ b₂ b₃ : D₀}
    {f : hom a₁ b₁} {g : hom a₂ b₂} {h : hom a₃ b₃}
    : vert_connect g h → vert_connect f g → vert_connect f h :=
  (λ v u, sigma.mk (v.1 ∘ u.1) (sigma.mk (v.2.1 ∘ u.2.1) (comp₁ v.2.2 u.2.2)))

  definition vert_assoc {f₁ f₂ f₃ f₄ : Σ (a b : D₀), hom a b}
    (Sw : vert_connect f₃ f₄)
    (Sv : vert_connect f₂ f₃)
    (Su : vert_connect f₁ f₂) : vert_comp Sw (vert_comp Sv Su) = vert_comp (vert_comp Sw Sv) Su


  definition vert_precat : precategory.{(max l₀ l₁) (max l₀ l₁ l₂)} (Σ (a b : D₀), hom a b) :=
  begin
    fapply precategory.mk.{(max l₀ l₁) (max l₀ l₁ l₂)},
                intros (S, T),
                exact (Σ (h : hom S.1 T.1) (i : hom S.2.1 T.2.1), D₂ S.2.2 T.2.2 h i),
              intros, apply trunc_sigma, apply !homH,
              intro f, apply trunc_sigma, apply !homH,
              intro g, apply !homH',
            intros (S, T, U, V, W), fapply sigma.mk, apply (comp (V.1) (W.1)),
            fapply sigma.mk, apply (@comp D₀ C S.2.1 T.2.1 U.2.1 (V.2.1) (W.2.1)),
            apply (@comp₁ D₀ C D₂ D S.1 S.2.1 T.1 T.2.1 U.1 U.2.1
              S.2.2 T.2.2), apply (V.2.2), apply (W.2.2),
          intros, fapply sigma.mk, exact (ID a.1),
          fapply sigma.mk, exact (ID a.2.1), apply (@ID₁ D₀ C D₂ D a.1 a.2.1 a.2.2),
        intros, fapply sigma.path, apply (@assoc D₀ C a.1 b.1 c.1 d.1 h.1 g.1 f.1),
        fapply sigma.path, exact (@assoc D₀ C a.2.1 b.2.1 c.2.1 d.2.1 h.2.1 g.2.1 f.2.1),
        apply (@assoc₁ D₀ C D₂ D a.1 a.2.1 b.1 b.2.1 c.1 c.2.1 d.1 d.2.1
          a.2.2 b.2.2 f.1 f.2.1 c.2.2 g.1 g.2.1 d.2.2 h.1 h.2.1 f.2.2 g.2.2 h.2.2),
  end

exit


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

  check zero

end dbl_precat
