import types.sigma
import .decl

open precategory morphism truncation eq sigma sigma.ops unit nat

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
  include C

  definition square_dbl_precat : dbl_precat C
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

  definition comm_square_dbl_precat : dbl_precat C
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

end dbl_precat

namespace dbl_precat
  context
  --universe variables l₀ l₁ l₂
  /-variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}
    [D : dbl_precat C D₂]-/
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : dbl_precat C D₂]
  --include D

  structure vert_ob : Type := (vo1 : D₀) (vo2 : D₀) (vo3 : hom vo1 vo2)

  structure vert_connect (Sf Sg : vert_ob) : Type :=
  (vc1 : hom (vert_ob.vo1 Sf) (vert_ob.vo1 Sg))
  (vc2 : hom (vert_ob.vo2 Sf) (vert_ob.vo2 Sg))
  (vc3 : D₂ (vert_ob.vo3 Sf) (vert_ob.vo3 Sg) vc1 vc2)

  open vert_ob vert_connect

  definition vert_connect_path' {Sf Sg : vert_ob} : Π
    {h₁ h₂ : hom (vo1 Sf) (vo1 Sg)}
    {i₁ i₂ : hom (vo2 Sf) (vo2 Sg)}
    (ph : h₁ = h₂)
    {u : D₂ (vo3 Sf) (vo3 Sg) h₁ i₁}
    (pi : i₁ = i₂)
    {v : D₂ (vo3 Sf) (vo3 Sg) h₂ i₂}
    (puv : pi ▹ ph ▹ u = v)
      , vert_connect.mk h₁ i₁ u  = vert_connect.mk h₂ i₂ v :=
  begin
    intros (h₁, h₂, i₁, i₂, ph), apply (eq.rec_on ph),
    intros (u, pi), apply (eq.rec_on pi),
    intros, apply (eq.rec_on puv),
    apply idp,
  end

  definition vert_comp [reducible] [D : dbl_precat C D₂] {Sf Sg Sh : vert_ob}
    : vert_connect Sg Sh → vert_connect Sf Sg → vert_connect Sf Sh :=
  (λ Sv Su, vert_connect.mk (vc1 Sv ∘ vc1 Su) (vc2 Sv ∘ vc2 Su)
    (comp₁ C (vc3 Sv) (vc3 Su)))

  definition vert_assoc [D : dbl_precat C D₂] {Sf₁ Sf₂ Sf₃ Sf₄ : vert_ob}
    (Sw : vert_connect Sf₃ Sf₄) (Sv : vert_connect Sf₂ Sf₃) (Su : vert_connect Sf₁ Sf₂)
    : vert_comp Sw (vert_comp Sv Su) = vert_comp (vert_comp Sw Sv) Su :=
  begin
    fapply vert_connect_path',
    exact (assoc (vc1 Sw) (vc1 Sv) (vc1 Su)),
    exact (assoc (vc2 Sw) (vc2 Sv) (vc2 Su)),
    exact (assoc₁ C (vc3 Sw) (vc3 Sv) (vc3 Su)),
  end

  /-sigma.path (@assoc D₀ C Sf₁.1 Sf₂.1 Sf₃.1 Sf₄.1 Sw.1 Sv.1 Su.1) (
    sigma.path (@assoc D₀ C Sf₁.2.1 Sf₂.2.1 Sf₃.2.1 Sf₄.2.1 Sw.2.1 Sv.2.1 Su.2.1)
      (@assoc₁ D₀ C D₂ D Sf₁.1 Sf₁.2.1 Sf₂.1 Sf₂.2.1 Sf₃.1 Sf₃.2.1 Sf₄.1 Sf₄.2.1
        Sf₁.2.2 Sf₂.2.2 Su.1 Su.2.1 Sf₃.2.2 Sv.1 Sv.2.1 Sf₄.2.2 Sw.1 Sw.2.1 Sw.2.2 Sv.2.2 Su.2.2)
    )-/
exit
  definition vert_assoc {Sf₁ Sf₂ Sf₃ Sf₄ : Σ (a b : D₀), @hom D₀ C a b}
    (Sw : vert_connect Sf₃ Sf₄) (Sv : vert_connect Sf₂ Sf₃) (Su : vert_connect Sf₁ Sf₂)
    : vert_comp Sw (vert_comp Sv Su) = vert_comp (vert_comp Sw Sv) Su :=
  sigma.path (@assoc D₀ C Sf₁.1 Sf₂.1 Sf₃.1 Sf₄.1 Sw.1 Sv.1 Su.1) (
    sigma.path (@assoc D₀ C Sf₁.2.1 Sf₂.2.1 Sf₃.2.1 Sf₄.2.1 Sw.2.1 Sv.2.1 Su.2.1)
      (@assoc₁ D₀ C D₂ D Sf₁.1 Sf₁.2.1 Sf₂.1 Sf₂.2.1 Sf₃.1 Sf₃.2.1 Sf₄.1 Sf₄.2.1
        Sf₁.2.2 Sf₂.2.2 Su.1 Su.2.1 Sf₃.2.2 Sv.1 Sv.2.1 Sf₄.2.2 Sw.1 Sw.2.1 Sw.2.2 Sv.2.2 Su.2.2)
    )

  definition vert_precat : precategory.{(max l₀ l₁) (max l₀ l₁ l₂)} (Σ (a b : D₀), hom a b) :=
  /-begin
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
  end-/ sorry

  /-definition bnd_upper (u : D₂ f g h i) := f
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

  check zero-/

end

end dbl_precat
