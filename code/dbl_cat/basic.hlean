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
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type}
    [D : dbl_precat C D₂]

  structure vert_ob : Type := (vo1 : D₀) (vo2 : D₀) (vo3 : hom vo1 vo2)

  definition vert_ob_sigma_char : (Σ (a b : D₀), hom a b) ≃ vert_ob :=
  begin
    fapply equiv.mk,
      intro S, apply (vert_ob.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, apply (vert_ob.rec_on V), intros (a, b, f),
        apply (⟨a, b, f⟩),
      intro V, apply (vert_ob.rec_on V), intros (a, b, f),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (a, S'),
    apply (sigma.rec_on S'), intros (b, f),
    apply idp,
  end

  structure vert_connect (Sf Sg : vert_ob) : Type :=
  (vc1 : hom (vert_ob.vo1 Sf) (vert_ob.vo1 Sg))
  (vc2 : hom (vert_ob.vo2 Sf) (vert_ob.vo2 Sg))
  (vc3 : D₂ (vert_ob.vo3 Sf) (vert_ob.vo3 Sg) vc1 vc2)

  open vert_ob vert_connect

  definition vert_connect_sigma_char (Sf Sg : vert_ob) :
    (Σ (h : hom (vo1 Sf) (vo1 Sg)) (i : hom (vo2 Sf) (vo2 Sg)), D₂ (vo3 Sf) (vo3 Sg) h i)
      ≃ vert_connect Sf Sg :=
  begin
    fapply equiv.mk,
      intro S, apply (vert_connect.mk S.1 S.2.1 S.2.2),
    fapply is_equiv.adjointify,
        intro V, apply (vert_connect.rec_on V), intros (h, i, u),
        exact (⟨h, i, u⟩),
      intro V, apply (vert_connect.rec_on V), intros (h, i, u),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (h, S'),
    apply (sigma.rec_on S'), intros (i, u),
    apply idp,
  end

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

  definition vert_id [D : dbl_precat C D₂] (Sf : vert_ob)
    : vert_connect Sf Sf :=
  vert_connect.mk (ID (vo1 Sf)) (ID (vo2 Sf)) (ID₁ D₂ (vo3 Sf))

  definition vert_assoc [D : dbl_precat C D₂] {Sf₁ Sf₂ Sf₃ Sf₄ : vert_ob}
    (Sw : vert_connect Sf₃ Sf₄) (Sv : vert_connect Sf₂ Sf₃) (Su : vert_connect Sf₁ Sf₂)
    : vert_comp Sw (vert_comp Sv Su) = vert_comp (vert_comp Sw Sv) Su :=
  begin
    fapply vert_connect_path',
    exact (assoc (vc1 Sw) (vc1 Sv) (vc1 Su)),
    exact (assoc (vc2 Sw) (vc2 Sv) (vc2 Su)),
    exact (assoc₁ C (vc3 Sw) (vc3 Sv) (vc3 Su)),
  end

  definition vert_id_left [D : dbl_precat C D₂] {Sf Sg : vert_ob}
    (Su : vert_connect Sf Sg) : vert_comp (vert_id Sg) Su = Su :=
  begin
    apply (vert_connect.rec_on Su),
    intros (h, i, u),
    fapply vert_connect_path',
    apply id_left,
    apply id_left,
    exact (id_left₁ C u),
  end

  definition vert_id_right [D : dbl_precat C D₂] {Sf Sg : vert_ob}
    (Su : vert_connect Sf Sg) : vert_comp Su (vert_id Sf) = Su :=
  begin
    apply (vert_connect.rec_on Su),
    intros (h, i, u),
    fapply vert_connect_path',
    apply id_right,
    apply id_right,
    exact (id_right₁ C u),
  end


--vert_comp (vert_id Sg) Su = Su

end

  universe variables l₀ l₁ l₂
  variables {D₀ : Type.{l₀}} [C : precategory.{l₀ (max l₀ l₁)} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d)
      (h : hom a c) (i : hom b d), Type.{max l₀ l₁ l₂}}
    [D : dbl_precat C D₂]

  definition vert_precat [D : dbl_precat C D₂]
    : precategory.{(max l₀ l₁) (max l₀ l₁ l₂)} vert_ob :=
  begin
    fapply precategory.mk.{(max l₀ l₁) (max l₀ l₁ l₂)},
                intros (Sf, Sg), exact (@vert_connect D₀ C D₂ Sf Sg),
              intros (Sf, Sg), apply trunc_equiv, apply equiv.to_is_equiv,
              exact (@vert_connect_sigma_char D₀ C D₂ Sf Sg),
              apply trunc_sigma, apply !homH,
              intro f, apply trunc_sigma, apply !homH,
              intro g, apply (@homH' D₀ C D₂ D),
            intros (Sf, Sg, Sh, Sv, Su), apply (vert_comp Sv Su),
          intro Sf, exact (@vert_id D₀ C D₂ D Sf),
        intros (Sf₁, Sf₂, Sf₃, Sf₄, Sw, Sv, Su),
        exact (@vert_assoc D₀ C D₂ D Sf₁ Sf₂ Sf₃ Sf₄ Sw Sv Su),
      intros (Sf, Sg, Su), exact (@vert_id_left D₀ C D₂ D Sf Sg Su),
    intros (Sf, Sg, Su), exact (@vert_id_right D₀ C D₂ D Sf Sg Su),
  end

end dbl_precat
