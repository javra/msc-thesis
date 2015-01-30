import ..dbl_gpd.basic ..xmod.decl

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod
open path_algebra

set_option pp.beta true
namespace gamma
  context
  universe variable l
  parameters {D₀ : Type.{l}}
    [D₀set : is_hset D₀]
    [C : groupoid.{l l} D₀]
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type.{l})
    [G : dbl_gpd C D₂]
  include G D₀set C

  structure M_morphism (a : D₀) : Type :=
    (lid : hom a a)
    (filler : D₂ lid id id id)

  definition M_morphism.sigma_char (a : D₀) :
    (Σ (lid : hom a a), D₂ lid id id id) ≃ (M_morphism a) :=
  begin
    fapply equiv.mk,
      intro P, apply (sigma.rec_on P), intros (lid, filler),
      exact (M_morphism.mk lid filler),
    fapply is_equiv.adjointify,
        intro P, apply (M_morphism.rec_on P), intros (lid, filler),
        exact ((⟨lid, filler⟩)),
      intro P, apply (M_morphism.rec_on P), intros (lid, filler),
      apply idp,
    intro P, apply (sigma.rec_on P), intros (lid, filler),
    apply idp,
  end

  protected definition M_morphism.is_hset (a : D₀) :
    is_hset (M_morphism a) :=
  begin
    apply trunc_equiv, apply equiv.to_is_equiv, apply M_morphism.sigma_char,
    apply trunc_sigma, apply !homH,
    intro f, apply (homH' D₂),
  end

  protected definition M_morphism.comp [reducible] {a: D₀} (v u : M_morphism a) : M_morphism a :=
  M_morphism.mk ((M_morphism.lid v) ∘ (M_morphism.lid u))
    (transport (λ x, D₂ ((M_morphism.lid v) ∘ (M_morphism.lid u)) x id id)
    (id_left (ID a)) (comp₂ D₂ (M_morphism.filler v) (M_morphism.filler u)))

  protected definition M_morphism.congr ⦃a : D₀⦄
    (f1 g1 : hom a a) (f2 : D₂ f1 id id id) (g2 : D₂ g1 id id id)
    (p1 : f1 = g1) (p2 :  p1 ▹ f2 = g2) :
      M_morphism.mk f1 f2 = M_morphism.mk g1 g2 :=
  begin
    apply (eq.rec_on p2),
    apply (eq.rec_on p1),
    apply idp,
  end

  protected definition M_morphism.assoc ⦃a b c d : D₀⦄ (M N O : M_morphism a) :
    M_morphism.comp M (M_morphism.comp N O) = M_morphism.comp (M_morphism.comp M N) O :=
  begin
    revert O, revert N, apply (M_morphism.rec_on M), intros (M1, M2),
    intro N, apply (M_morphism.rec_on N), intros (N1, N2),
    intro O, apply (M_morphism.rec_on O), intros (M1, M2),
    fapply M_morphism.congr,
      apply !assoc,
      exact sorry,
  end

  protected definition M_morphism.one [reducible] (a : D₀) : M_morphism a :=
  begin
    fapply M_morphism.mk, apply (ID a), apply (ID₂ D₂ (ID a)),
  end

  definition transport_commute {A B : Type} (P : A → B → Type)
    {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    {P1 : P a b} :
    p ▹ q ▹ P1 = q ▹ p ▹ P1 :=
  begin
    revert P1,
    apply (eq.rec_on p), apply (eq.rec_on q),
    intros, apply idp,
  end

  protected definition M_morphism.id_left ⦃a : D₀⦄ (M : M_morphism a) :
    M_morphism.comp (M_morphism.one a) M = M :=
  begin
    apply (M_morphism.rec_on M), intros (lid, filler),
    fapply (M_morphism.congr),
      apply (id_left lid),
      apply concat, rotate 3, apply (id_left₂ D₂ filler),
      apply transport_commute,
  end

  definition id_left_id_eq_id_right_id ⦃ a : D₀ ⦄ : (id_left (ID a)) = (id_right (ID a)) :=
  begin
    apply is_hset.elim,
  end

  protected definition M_morphism.id_right ⦃a : D₀⦄ (M : M_morphism a) :
    M_morphism.comp M (M_morphism.one a) = M :=
  begin
    apply (M_morphism.rec_on M), intros (lid, filler),
    fapply (M_morphism.congr),
      apply (id_right lid),
      apply concat, rotate 3, apply (id_right₂ D₂ filler),
      apply concat, apply transport_commute,
      apply (transport _ (!id_left_id_eq_id_right_id)),
      apply idp,
  end

  --TODO: Think of something better to prevent such ambiguities
  definition iso_of_id' {a : D₀} : @morphism.inverse D₀ C a a (ID a) (all_iso (ID a)) = id :=
  inverse_eq_intro_left !id_compose

  definition M_morphism.inv_aux ⦃a : D₀⦄ (u : M_morphism a) :
    D₂ ((M_morphism.lid u)⁻¹) id id id :=
  iso_of_id' ▹ (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler  u))

  definition M_morphism.inv [reducible] ⦃a : D₀⦄ (u : M_morphism a) :
    M_morphism a :=
  begin
    fapply M_morphism.mk,
      apply ((M_morphism.lid u)⁻¹),
      exact (M_morphism.inv_aux u),
  end

  definition M_morphism.inverse_compose_aux_aux {a : D₀} (v u : M_morphism a)
    {g : hom a a} (p : id⁻¹ = g) :
  (comp₂ D₂ (transport (λ x, D₂ ((M_morphism.lid v)⁻¹) x id id) p
    (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler v))) (M_morphism.filler u))
    = p ▹ (comp₂ D₂ (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler v)) (M_morphism.filler u)) :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  definition M_morphism.inverse_compose_aux1 {a : D₀} (u : M_morphism a) :
    (comp₂ D₂ (M_morphism.filler (M_morphism.inv u)) (M_morphism.filler u))
    = iso_of_id' ▹
    (comp₂ D₂ (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler u)) (M_morphism.filler u)) :=
  (M_morphism.inverse_compose_aux_aux u u iso_of_id')

  definition M_morphism.inverse_compose_aux4 {a : D₀} (u : M_morphism a) :=
  ap (λ x, (transport (λ (a_2 : hom a a), D₂ (ID a) a_2 id id) (id_left id)
       (transport (λ (a_3 : hom a a), D₂ a_3 (compose id id) id id)
          (inverse_compose (M_morphism.lid u)) x)))
    (M_morphism.inverse_compose_aux1 u)

  definition M_morphism.inverse_compose_aux5 {a : D₀}
    {f1 f5 : hom a a} {g1 g1' g3 g4 : hom a a}
    (filler : D₂ f1 (g1 ∘ g1') (ID a) (ID a))
    (p1 : f1 = f5) (p2 : g1 ∘ g1' = g3) (p3 : g1 = g4) (p4 : f1 = f5) (p5 : @comp D₀ C a a a g4 g1' = g3) :
    p5 ▹ p4 ▹ p3 ▹ filler
    = (transport (λ x, D₂ f5 x id id) p2
      (transport (λ x, D₂ x (g1 ∘ g1') id id) p1 filler)) :=
  begin
    revert p1, revert p2, revert p3, revert p4, apply (eq.rec_on p5),
    intro p4, apply (eq.rec_on p4), intro p3, apply (eq.rec_on p3), intro p2, intro p1,
    assert (p1refl : idp = p1), apply is_hset.elim, apply (transport _ p1refl),
    assert (p2refl : idp = p2), apply is_hset.elim, apply (transport _ p2refl),
    apply idp,
  end

  definition M_morphism.inverse_compose ⦃a : D₀⦄ (u : M_morphism a) :
    M_morphism.comp (M_morphism.inv u) u = M_morphism.one a :=
  begin
    apply (M_morphism.rec_on u), intros (lid, filler),
    fapply (M_morphism.congr),
      apply inverse_compose,
      apply concat, rotate 3, apply (weak_dbl_gpd.inverse_compose₂ D₂ filler),
      apply concat, apply transport_commute,
      apply concat, apply M_morphism.inverse_compose_aux4,
      apply M_morphism.inverse_compose_aux5,
  end

  open M_morphism
  protected definition M (a : D₀) : group (M_morphism a) :=
  begin
    fapply group.mk,
      intros (u, v), apply (comp u v),
      apply (M_morphism.is_hset a),
      intros (u, v, w), apply ((assoc u v w)⁻¹),
      apply M_morphism.one,
      intro u, apply (id_left u),
      intro u, apply (id_right u),
      intro u, apply (inv D₂ u),
      intro u, apply (inverse_compose u),
  end


  end
end gamma

    /-fapply groupoid.mk,
      intros (a, b), exact (M_morphism a b),
      intros (a, b), exact (M_morphism.is_hset a b),
      intros (a, b, c, M, N), exact (@M_morphism.comp a b c M N),
      intros,  fapply M_morphism.mk,
        apply idp, apply id, apply (ID₂ D₂ id),-/
      --intros (a, b, c, d, M),
