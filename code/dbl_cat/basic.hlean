import types.sigma types.pi
import .decl

open precategory morphism truncation eq sigma sigma.ops unit nat
open equiv pi

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
      intros, apply succ_is_trunc, apply trunc_succ, apply !homH,
      intros, exact (calc (i₂ ∘ i₁) ∘ f₁ = i₂ ∘ i₁ ∘ f₁ : assoc
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

  variables {a b c d a₂ b₂ c₂ d₂ d₃ d₄ : D₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {f₂ : hom b b₂} {g₂ : hom d d₂} {i₂ : hom b₂ d₂}
    {g₃ : hom c₂ d₃} {h₂ : hom c c₂} {i₃ : hom d d₃}
    (u : D₂ f g h i)

  infixl `+₁`:65 := λ {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type} {a b c₁ d₁ c₂ d₂ : D₀}
    {f₁ : hom a b} {g₁ : hom c₁ d₁} {h₁ : hom a c₁} {i₁ : hom b d₁}
    {g₂ : hom c₂ d₂} {h₂ : hom c₁ c₂} {i₂ : hom d₁ d₂}
    (u : D₂ f₁ g₁ h₁ i₁) (v : D₂ g₁ g₂ h₂ i₂), comp₁ v u

end dbl_precat

namespace worm_precat
  context
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : worm_precat C D₂]
  include D

  structure two_cell_ob : Type := (vo1 : D₀) (vo2 : D₀) (vo3 : hom vo1 vo2)

  definition two_cell_ob_sigma_char : (Σ (a b : D₀), hom a b) ≃ two_cell_ob :=
  begin
    fapply equiv.mk,
      intro S, apply (two_cell_ob.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, apply (two_cell_ob.rec_on V), intros (a, b, f),
        apply (⟨a, b, f⟩),
      intro V, apply (two_cell_ob.rec_on V), intros (a, b, f),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (a, S'),
    apply (sigma.rec_on S'), intros (b, f),
    apply idp,
  end

  structure two_cell_connect (Sf Sg : two_cell_ob) : Type :=
  (vc1 : hom (two_cell_ob.vo1 Sf) (two_cell_ob.vo1 Sg))
  (vc2 : hom (two_cell_ob.vo2 Sf) (two_cell_ob.vo2 Sg))
  (vc3 : D₂ (two_cell_ob.vo3 Sf) (two_cell_ob.vo3 Sg) vc1 vc2)

  open two_cell_ob two_cell_connect

  definition two_cell_connect_sigma_char (Sf Sg : two_cell_ob) :
    (Σ (h : hom (vo1 Sf) (vo1 Sg)) (i : hom (vo2 Sf) (vo2 Sg)), D₂ (vo3 Sf) (vo3 Sg) h i)
      ≃ two_cell_connect Sf Sg :=
  begin
    fapply equiv.mk,
      intro S, apply (two_cell_connect.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, apply (two_cell_connect.rec_on V), intros (h, i, u),
        exact (⟨h, i, u⟩),
      intro V, apply (two_cell_connect.rec_on V), intros (h, i, u),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (h, S'),
    apply (sigma.rec_on S'), intros (i, u),
    apply idp,
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
    intros (h₁, h₂, i₁, i₂, ph), apply (eq.rec_on ph),
    intros (u, pi), apply (eq.rec_on pi),
    intros, apply (eq.rec_on puv),
    apply idp,
  end

  set_option pp.universes true
  include D
  definition two_cell_comp [reducible] {Sf Sg Sh : two_cell_ob}
    : two_cell_connect Sg Sh → two_cell_connect Sf Sg → two_cell_connect Sf Sh :=
  (λ Sv Su, two_cell_connect.mk (vc1 Sv ∘ vc1 Su) (vc2 Sv ∘ vc2 Su)
    (comp₁ D₂ (vc3 Sv) (vc3 Su)))

  definition two_cell_id (Sf : two_cell_ob)
    : two_cell_connect Sf Sf :=
  two_cell_connect.mk (ID (vo1 Sf)) (ID (vo2 Sf)) (ID₁ D₂ (vo3 Sf))

  definition two_cell_assoc {Sf₁ Sf₂ Sf₃ Sf₄ : two_cell_ob}
    (Sw : two_cell_connect Sf₃ Sf₄) (Sv : two_cell_connect Sf₂ Sf₃) (Su : two_cell_connect Sf₁ Sf₂)
    : two_cell_comp Sw (two_cell_comp Sv Su) = two_cell_comp (two_cell_comp Sw Sv) Su :=
  begin
    fapply two_cell_connect_path',
    exact (assoc (vc1 Sw) (vc1 Sv) (vc1 Su)),
    exact (assoc (vc2 Sw) (vc2 Sv) (vc2 Su)),
    exact (assoc₁ C (vc3 Sw) (vc3 Sv) (vc3 Su)),
  end

  definition two_cell_id_left [D : worm_precat C D₂] {Sf Sg : two_cell_ob}
    (Su : two_cell_connect Sf Sg) : two_cell_comp (two_cell_id Sg) Su = Su :=
  begin
    apply (two_cell_connect.rec_on Su),
    intros (h, i, u),
    fapply two_cell_connect_path',
    apply id_left,
    apply id_left,
    exact (id_left₁ C u),
  end

  definition two_cell_id_right [D : worm_precat C D₂] {Sf Sg : two_cell_ob}
    (Su : two_cell_connect Sf Sg) : two_cell_comp Su (two_cell_id Sf) = Su :=
  begin
    apply (two_cell_connect.rec_on Su),
    intros (h, i, u),
    fapply two_cell_connect_path',
    apply id_right,
    apply id_right,
    exact (id_right₁ C u),
  end

end

  universe variables l₀ l₁ l₂
  variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}

  definition two_cell_precat [D : worm_precat C D₂]
    : precategory.{(max l₀ l₁) (max l₀ l₁ l₂)} two_cell_ob :=
  begin
    fapply precategory.mk.{(max l₀ l₁) (max l₀ l₁ l₂)},
                intros (Sf, Sg), exact (@two_cell_connect D₀ C D₂ Sf Sg),
              intros (Sf, Sg), apply trunc_equiv, apply equiv.to_is_equiv,
              exact (@two_cell_connect_sigma_char D₀ C D₂ Sf Sg),
              apply trunc_sigma, apply !homH,
              intro f, apply trunc_sigma, apply !homH,
              intro g, apply (@homH' D₀ C D₂ D),
            intros (Sf, Sg, Sh, Sv, Su), apply (two_cell_comp Sv Su),
          intro Sf, exact (@two_cell_id D₀ C D₂ D Sf),
        intros (Sf₁, Sf₂, Sf₃, Sf₄, Sw, Sv, Su),
        exact (@two_cell_assoc D₀ C D₂ D Sf₁ Sf₂ Sf₃ Sf₄ Sw Sv Su),
      intros (Sf, Sg, Su), exact (@two_cell_id_left D₀ C D₂ D Sf Sg Su),
    intros (Sf, Sg, Su), exact (@two_cell_id_right D₀ C D₂ D Sf Sg Su),
  end

end worm_precat

namespace dbl_precat
  universe variables l₀ l₁ l₂
  variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}

  definition vert_precat [D : dbl_precat C D₂] :=
  @worm_precat.two_cell_precat.{l₀ l₁ l₂} D₀ C D₂ (to_worm_precat_1 D₂)

  definition horiz_precat [D : dbl_precat C D₂] :=
  @worm_precat.two_cell_precat.{l₀ l₁ l₂} D₀ C _ (to_worm_precat_2 D₂)

  definition zero [D : dbl_precat C D₂] (a : D₀) := ID₁ D₂ (ID a)
  notation `◻` := !zero


end dbl_precat
