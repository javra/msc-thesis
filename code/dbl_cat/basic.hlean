import types.sigma types.pi
import .decl

open category is_trunc eq sigma sigma.ops unit nat
open equiv pi

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
  include C

  definition square_dbl_precat : dbl_precat C
    (λ ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), unit) :=
  begin
    fapply dbl_precat.mk,
      repeat (intros; (rexact ⋆ |  apply is_hprop.elim | apply is_trunc_succ)),
      repeat (intros;  apply idp)
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
      repeat (intros; apply is_hset.elim),
      intros, apply is_trunc_eq,
      intros, exact (calc (i₂ ∘ i₁) ∘ f₁ = i₂ ∘ i₁ ∘ f₁ : assoc
                                     ... = i₂ ∘ g₁ ∘ h₁ : a_2
                                     ... = (i₂ ∘ g₁) ∘ h₁ : assoc
                                     ... = (g₂ ∘ h₂) ∘ h₁ : a_1
                                     ... = g₂ ∘ h₂ ∘ h₁ : assoc),
      intros, exact (calc ID b ∘ f = f : id_left
                               ... = f ∘ ID a : id_right),
      repeat (intros; apply is_hset.elim),
      intros, apply is_trunc_eq,
      repeat (intros; apply is_hset.elim),
  end

end dbl_precat

namespace worm_precat
  context
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    (D : worm_precat C D₂)

  include D₀ C D
  structure two_cell_ob :=
    (vo1 vo2 : D₀)
    (vo3 : hom vo1 vo2)

  structure two_cell_connect (Sf Sg : two_cell_ob) :=
    (vc1 : hom (two_cell_ob.vo1 Sf) (two_cell_ob.vo1 Sg))
    (vc2 : hom (two_cell_ob.vo2 Sf) (two_cell_ob.vo2 Sg))
    (vc3 : D₂ (two_cell_ob.vo3 Sf) (two_cell_ob.vo3 Sg) vc1 vc2)

  definition two_cell_ob_sigma_char : (Σ (a b : D₀), hom a b) ≃ two_cell_ob :=
  begin
    fapply equiv.mk,
      intro S, apply (two_cell_ob.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, cases V with [a, b, f], apply (⟨a, b, f⟩),
      intro V, cases V, apply idp,
    intro S, cases S with [a, S'],
    cases S', apply idp,
  end

  open two_cell_ob two_cell_connect

  definition two_cell_connect_sigma_char (Sf Sg : two_cell_ob) :
    (Σ (h : hom (vo1 Sf) (vo1 Sg)) (i : hom (vo2 Sf) (vo2 Sg)), D₂ (vo3 Sf) (vo3 Sg) h i)
      ≃ two_cell_connect Sf Sg :=
  begin
    fapply equiv.mk,
      intro S, apply (two_cell_connect.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, cases V with [h, i, u], exact (⟨h, i, u⟩),
      intro V, cases V, apply idp,
    intro S, cases S with [h, S'],
    cases S', apply idp,
  end

  definition two_cell_connect_path' {Sf Sg : two_cell_ob} : Π
    {h₁ h₂ : hom (vo1 Sf) (vo1 Sg)}
    {i₁ i₂ : hom (vo2 Sf) (vo2 Sg)}
    (ph : h₁ = h₂)
    {u : D₂ (vo3 Sf) (vo3 Sg) h₁ i₁}
    (pi : i₁ = i₂)
    {v : D₂ (vo3 Sf) (vo3 Sg) h₂ i₂}
    (puv : pi ▹ ph ▹ u = v)
      , two_cell_connect.mk h₁ i₁ u  = two_cell_connect.mk h₂ i₂ v :=
  begin
    intros [h₁, h₂, i₁, i₂, ph], cases ph,
    intros [u, pi], cases pi,
    intros, cases puv,
    apply idp,
  end

  definition two_cell_comp [reducible] {Sf Sg Sh : two_cell_ob}
    : two_cell_connect Sg Sh → two_cell_connect Sf Sg → two_cell_connect Sf Sh :=
  (λ Sv Su, two_cell_connect.mk (vc1 Sv ∘ vc1 Su) (vc2 Sv ∘ vc2 Su)
    (@comp₁ D₀ C D₂ D _ _ _ _ _ _ _ _ _ _ _ _ _ (vc3 Sv) (vc3 Su)))

  definition two_cell_id (Sf : two_cell_ob)
    : two_cell_connect Sf Sf :=
  two_cell_connect.mk (ID (vo1 Sf)) (ID (vo2 Sf)) (@ID₁ D₀ C D₂ D _ _ (vo3 Sf))

  definition two_cell_assoc {Sf₁ Sf₂ Sf₃ Sf₄ : two_cell_ob}
    (Sw : two_cell_connect Sf₃ Sf₄) (Sv : two_cell_connect Sf₂ Sf₃) (Su : two_cell_connect Sf₁ Sf₂)
    : two_cell_comp Sw (two_cell_comp Sv Su) = two_cell_comp (two_cell_comp Sw Sv) Su :=
  begin
    fapply two_cell_connect_path',
    exact (assoc (vc1 Sw) (vc1 Sv) (vc1 Su)),
    exact (assoc (vc2 Sw) (vc2 Sv) (vc2 Su)),
    apply assoc₁,
  end

  definition two_cell_id_left {Sf Sg : two_cell_ob}
    (Su : two_cell_connect Sf Sg) : two_cell_comp (two_cell_id Sg) Su = Su :=
  begin
    cases Su,
    fapply two_cell_connect_path',
    apply id_left,
    apply id_left,
    apply id_left₁,
  end

  definition two_cell_id_right {Sf Sg : two_cell_ob}
    (Su : two_cell_connect Sf Sg) : two_cell_comp Su (two_cell_id Sf) = Su :=
  begin
    cases Su,
    fapply two_cell_connect_path',
    apply id_right,
    apply id_right,
    apply id_right₁,
  end

end

  universe variables l₀ l₁ l₂
  variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}

  definition two_cell_precat (D : worm_precat C D₂)
    : precategory.{(max l₀ l₁) (max l₀ l₁ l₂)} (two_cell_ob D) :=
  begin
    fapply precategory.mk.{(max l₀ l₁) (max l₀ l₁ l₂)},
      intros [Sf, Sg], exact (two_cell_connect D Sf Sg),
      intros [Sf, Sg], apply is_trunc_is_equiv_closed, apply equiv.to_is_equiv,
        exact (two_cell_connect_sigma_char D Sf Sg),
        apply is_trunc_sigma, intros,
        apply is_trunc_sigma, intros, apply (homH' D),
      intros [Sf, Sg, Sh, Sv, Su], apply (two_cell_comp D Sv Su),
      intro Sf, exact (two_cell_id D Sf),
      intros, exact (two_cell_assoc D h g f),
      intros [Sf, Sg, Su], exact (two_cell_id_left D Su),
      intros [Sf, Sg, Su], exact (two_cell_id_right D Su),
  end

end worm_precat

namespace dbl_precat
  universe variables l₀ l₁ l₂
  variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}

  definition vert_precat (D : dbl_precat C D₂) :=
  worm_precat.two_cell_precat.{l₀ l₁ l₂} (to_worm_precat_1 D)

  definition horiz_precat (D : dbl_precat C D₂) :=
  worm_precat.two_cell_precat.{l₀ l₁ l₂} (to_worm_precat_2 D)

  definition zero [D : dbl_precat C D₂] (a : D₀) := ID₁ D (ID a)

end dbl_precat
