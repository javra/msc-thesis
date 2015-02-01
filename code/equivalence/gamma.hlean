import ..dbl_gpd.basic ..xmod.decl

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod
open path_algebra

--TODO make this file compile faster!

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

  protected definition M_morphism.comp [reducible] {a: D₀} (v u : M_morphism a) :
    M_morphism a :=
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

  definition transport_commute {A B : Type} (P : A → B → Type)
    {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    {P1 : P a b} :
    p ▹ q ▹ P1 = q ▹ p ▹ P1 :=
  begin
    revert P1,
    apply (eq.rec_on p), apply (eq.rec_on q),
    intros, apply idp,
  end

  protected definition M_morphism.assoc_bl_transport {a : D₀} {lid1 lid2 f g : hom a a}
    (filler1 : D₂ lid1 id id id) (filler2 : D₂ lid2 f id id) (p : f = g) :
    transport (λ x, D₂ _ (id ∘ x) id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ filler1 (p ▹ filler2) :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  protected definition M_morphism.assoc_br_transport {a : D₀} {lid1 lid2 f g : hom a a}
    (filler1 : D₂ lid1 f id id) (filler2 : D₂ lid2 id id id) (p : f = g) :
    transport (λ x, D₂ _ (x ∘ id) id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ (p ▹ filler1) filler2 :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  protected definition M_morphism.assoc_aux {a : D₀} (w v u : M_morphism a) :
    comp₂ D₂ (M_morphism.filler w) (M_morphism.filler (M_morphism.comp v u))
    = transport (λ x, D₂ _ (id ∘ x) id id) (id_left id)
    (comp₂ D₂ (M_morphism.filler w) (comp₂ D₂ (M_morphism.filler v)
      (M_morphism.filler u))) :=
  begin
    apply (!M_morphism.assoc_bl_transport⁻¹),
  end

  protected definition M_morphism.assoc_aux2 {a : D₀} (w v u : M_morphism a) :
    comp₂ D₂ (M_morphism.filler (M_morphism.comp w v)) (M_morphism.filler u)
    = transport (λ x, D₂ _ (x ∘ id) id id) (id_left id)
    (comp₂ D₂ (comp₂ D₂ (M_morphism.filler w) (M_morphism.filler v))
      (M_morphism.filler u)) :=
  begin
    apply (!M_morphism.assoc_br_transport⁻¹),
  end

  protected definition M_morphism.assoc_aux4 {a : D₀}
    {lid f f' g g' : hom a a} (filler : D₂ lid (g ∘ f) id id)
    (p : f = f') (q : g = g') (r : g ∘ f = g' ∘ f'):
    transport (λ x, D₂ lid (x ∘ f') id id) q
      (transport (λ x, D₂ lid (g ∘ x) id id) p filler)
    = transport (λ x, D₂ lid x id id) r filler :=
  begin
    revert r, revert p, apply (eq.rec_on q),
    intro p, apply (eq.rec_on p),
    intro r, assert (P : idp = r),
      apply is_hset.elim,
    apply (transport _ P),
    apply idp,
  end

  protected definition M_morphism.assoc_aux3 {a : D₀} {lid : hom a a}
    (filler : D₂ lid (id ∘ (id ∘ id)) id id) :
    transport (λ (x : hom a a), D₂ lid (x ∘ id) id id) (inverse (id_left id))
      (transport (λ (x : hom a a), D₂ lid (id ∘ x) id id) (id_left id) filler)
    = transport (λ x, D₂ lid x id id) (assoc id id id) filler :=
  begin
    apply M_morphism.assoc_aux4,
  end

  protected definition M_morphism.assoc ⦃a : D₀⦄ (w v u : M_morphism a) :
    M_morphism.comp w (M_morphism.comp v u) = M_morphism.comp (M_morphism.comp w v) u :=
  begin
    revert u, revert v, apply (M_morphism.rec_on w), intros (w1, w2),
    intro v, apply (M_morphism.rec_on v), intros (v1, v2),
    intro u, apply (M_morphism.rec_on u), intros (u1, u2),
    fapply M_morphism.congr,
      apply !assoc, apply concat,
      apply transport_commute,
      apply (ap (transport (λ (a_2 : hom a a), D₂ _ a_2 id id) (id_left id))),
      apply concat,
      apply (ap (transport (λ (a_3 : hom a a), D₂ a_3 (compose id id) id id)
       (assoc (M_morphism.lid (M_morphism.mk w1 w2)) (M_morphism.lid (M_morphism.mk v1 v2))
         (M_morphism.lid (M_morphism.mk u1 u2))))),
      apply M_morphism.assoc_aux,
      apply concat, rotate 3, apply inverse,
      apply M_morphism.assoc_aux2,
      apply concat,
      apply (transport_commute (λ x y, D₂ x (id ∘ y) id id)
        (assoc (M_morphism.lid (M_morphism.mk w1 w2))
          (M_morphism.lid (M_morphism.mk v1 v2)) (M_morphism.lid (M_morphism.mk u1 u2)))
        (id_left id)),
      apply moveL_transport_p,
      apply concat, apply M_morphism.assoc_aux3,
      apply assoc₂,
  end

  protected definition M_morphism.one [reducible] (a : D₀) : M_morphism a :=
  begin
    fapply M_morphism.mk, apply (ID a), apply (ID₂ D₂ (ID a)),
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
  definition iso_of_id' {a : D₀} :
    @morphism.inverse D₀ C a a (ID a) (all_iso (ID a)) = id :=
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
    (p1 : f1 = f5) (p2 : g1 ∘ g1' = g3) (p3 : g1 = g4) (p4 : f1 = f5) (p5 : g4 ∘ g1' = g3) :
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

  protected definition M [instance] (a : D₀) : group (M_morphism a) :=
  begin
    fapply group.mk,
      intros (u, v), apply (M_morphism.comp u v),
      apply (M_morphism.is_hset a),
      intros (u, v, w), apply ((M_morphism.assoc u v w)⁻¹),
      apply M_morphism.one,
      intro u, apply (M_morphism.id_left u),
      intro u, apply (M_morphism.id_right u),
      intro u, apply (M_morphism.inv u),
      intro u, apply (M_morphism.inverse_compose u),
  end

  protected definition mu [reducible] ⦃x : D₀⦄ (u : M_morphism x) : hom x x :=
  M_morphism.lid u

  protected definition mu_respect_comp ⦃x : D₀⦄ (v u : M_morphism x) :
    mu (v * u) = mu v ∘ mu u :=
  idp

  protected definition mu_respect_id ⦃x : D₀⦄ (u : M_morphism x) : mu 1 = ID x :=
  idp

  protected definition phi [reducible] ⦃x y : D₀⦄ (a : hom x y) (u : M_morphism x) :
    M_morphism y :=
  begin
    fapply M_morphism.mk,
      apply (a ∘ (M_morphism.lid u) ∘ a⁻¹),
    assert (v : D₂ (a ∘ (M_morphism.lid u) ∘ a⁻¹) (a ∘ id ∘ a⁻¹) id id),
      apply (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ (M_morphism.filler u) (ID₁ D₂ (a⁻¹)))),
    apply (transport (λ x, D₂ _ x id id) (compose_inverse a)
             (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (a⁻¹)) v)),
  end

  protected definition phi_respect_id_aux ⦃y : D₀⦄ {lid bottom : hom y y}
    (filler : D₂ lid bottom id id) :
    comp₂ D₂ (ID₂ D₂ (ID y)) filler
    = transport (λ x, D₂ x _ id id) ((id_left lid)⁻¹)
      (transport (λ x, D₂ lid x id id) ((id_left bottom)⁻¹) filler) :=
  begin
    apply moveL_transport_V, apply moveL_transport_V,
    apply id_left₂,
  end

  protected definition phi_respect_id_aux2 ⦃y : D₀⦄ {lid bottom : hom y y}
    (filler : D₂ lid bottom id id) :
    comp₂ D₂ filler (ID₂ D₂ (ID y))
    = transport (λ x, D₂ x _ id id) ((id_right lid)⁻¹)
      (transport (λ x, D₂ lid x id id) ((id_right bottom)⁻¹) filler) :=
  begin
    apply moveL_transport_V, apply moveL_transport_V,
    apply id_right₂,
  end

  variables ⦃y : D₀⦄
    (f1 f2 f3 f4 g0 g1 g2 g3 g4 g5 g6 g7 : hom y y)
    (p8 : f1 = f2) (p7 : g0 = g1 ∘ g2) (p6 : g2 = @comp D₀ C y y y g3 g4)
    (p5 : f2 = f3 ∘ f4) (p4 : g1 ∘ (g3 ∘ g4) = g5 ∘ g6)
    (p3 : g6 = g7) (p2 : f3 ∘ f4 = f1) (p1 : g5 ∘ g7 = g0)
    (filler : D₂ f1 g0 id id)-- :=

  protected definition phi_respect_id_aux3_aux
  := (transport (λ (x : hom y y), D₂ f1 x id id) p1
     (transport (λ (x : hom y y), D₂ x (g5 ∘ g7) id id) p2
      (transport (λ (x : hom y y), D₂ (f3 ∘ f4) (g5 ∘ x) id id) p3
       (transport (λ (x : hom y y), D₂ (f3 ∘ f4) x id id) p4
        (transport (λ (x : hom y y), D₂ x (g1 ∘ (g3 ∘ g4)) id id) p5
         (transport (λ (x : hom y y), D₂ f2 (g1 ∘ x) id id) p6
          (transport (λ (x : hom y y), D₂ f2 x id id) p7
           (transport (λ (x : hom y y), D₂ x g0 id id) p8 filler))))))))

  protected definition phi_respect_id_aux3 :
    phi_respect_id_aux3_aux f1 f2 f3 f4 g0 g1 g2 g3 g4 g5 g6 g7
      p8 p7 p6 p5 p4 p3 p2 p1 filler = filler :=
  begin
    revert filler, revert p4,
    revert p7, revert p5,
    revert p2, revert g1,
    revert p3, revert g6,
    revert p1, revert g0,
    apply (eq.rec_on p8),
    intro g0, intro p1, apply (eq.rec_on p1),
    intro g6, intro p3, apply (eq.rec_on p3),
    intro g1, intro p2, apply (eq.rec_on p2),
    intro p5,
    assert (p5_idp : idp = p5), apply is_hset.elim,
    apply (transport _ p5_idp),
    revert p6, revert g2,
    intros,
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    revert p4, revert p7, generalize (p6⁻¹), clear p6, revert g2,
    intro g2, intro p6inv, apply (eq.rec_on p6inv), intros,
    apply moveL_transport_V, apply moveL_transport_V,
    assert (P : idp ▹ refl (comp g3 g4) ▹ p7 ▹ refl (f3 ∘ f4) ▹ filler
      = p7 ▹ refl (f3 ∘ f4) ▹ filler),
      apply idp,
    apply concat, exact P, apply moveL_transport_V,
    apply concat, apply (!transport_pp⁻¹),
    assert (p74_idp : idp = p7 ⬝ p4),  apply is_hset.elim,
    apply (transport (λ x, x ▹ _ = _) p74_idp),
    apply idp,
  end

  --set_option pp.notation false
  --set_option pp.implicit true
  protected definition phi_respect_id ⦃y : D₀⦄ (u : M_morphism y) :
    phi (ID y) u = u :=
  begin
    apply (M_morphism.rec_on u), intros (lid, filler),
    fapply (M_morphism.congr),
      apply (transport _ (iso_of_id'⁻¹)),
      apply concat, apply id_left, apply id_right,
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    apply (transport (λ x, comp₂ D₂ x _ = _) ((zero_unique D₂ y)⁻¹)),
    apply concat, apply phi_respect_id_aux,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply (moveL_transport_V _ _ _ _ (apD (λ x, comp₂ D₂ filler (ID₁ D₂ x)) (@iso_of_id' y))),
    apply moveR_transport_V,
    apply (transport (λ x, comp₂ D₂ _ x = _) ((zero_unique D₂ y)⁻¹)),
    apply concat, apply phi_respect_id_aux2,
    apply moveR_transport_V, apply moveR_transport_V,
    apply (!phi_respect_id_aux3⁻¹),
  end

  end
end gamma
