import ..dbl_gpd.basic ..xmod.decl ..transport4

open dbl_precat eq iso category is_trunc nat
open equiv sigma sigma.ops prod path_algebra
set_option apply.class_instance false -- disable class instance resolution in the apply tactic

--TODO make this file compile faster!

set_option pp.beta true
namespace gamma
  context
  universe variable l
  parameters {D₀ : Type.{l}}
    [D₀set : is_hset D₀]
    [C : groupoid.{l l} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type.{l}}
    [G : dbl_gpd C D₂]
  include G D₀set C

  structure M_morphism (a : D₀) : Type :=
    (lid : hom a a)
    (filler : D₂ lid id id id)

  definition M_morphism.sigma_char (a : D₀) :
    (Σ (lid : hom a a), D₂ lid id id id) ≃ (M_morphism a) :=
  begin
    fapply equiv.mk,
      intro P, apply (sigma.rec_on P), intros [lid, filler],
      exact (M_morphism.mk lid filler),
    fapply is_equiv.adjointify,
        intro P, apply (M_morphism.rec_on P), intros [lid, filler],
        exact ((⟨lid, filler⟩)),
      intro P, apply (M_morphism.rec_on P), intros [lid, filler],
      apply idp,
    intro P, apply (sigma.rec_on P), intros [lid, filler],
    apply idp,
  end

  protected definition M_morphism.is_hset (a : D₀) : is_hset (M_morphism a) :=
  begin
    apply is_trunc_is_equiv_closed, apply equiv.to_is_equiv, apply (M_morphism.sigma_char a),
    apply is_trunc_sigma, apply !homH,
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

  protected definition M_morphism.congr' {a : D₀} (v u : M_morphism a)
    (p1 : M_morphism.lid v = M_morphism.lid u)
    (p2 : p1 ▹ M_morphism.filler v = M_morphism.filler u) : v = u :=
  begin
    cases v, cases u, apply M_morphism.congr, apply p2,
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

  protected definition M_morphism.assoc_bl_transport {a : D₀} {lid1 lid2 f1 f2 g : hom a a}
    (filler1 : D₂ lid1 f1 id id) (filler2 : D₂ lid2 f2 id id) (p : f2 = g) :
    transport (λ x, D₂ _ (f1 ∘ x) id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ filler1 (p ▹ filler2) :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  protected definition M_morphism.assoc_br_transport {a : D₀} {lid1 lid2 f1 f2 g : hom a a}
    (filler1 : D₂ lid1 f1 id id) (filler2 : D₂ lid2 f2 id id) (p : f1 = g) :
    transport (λ x, D₂ _ (x ∘ f2) id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ (p ▹ filler1) filler2 :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  protected definition M_morphism.assoc_ul_transport {a : D₀} {lid1 lid2 f1 f2 g : hom a a}
    (filler1: D₂ lid1 f1 id id) (filler2 : D₂ lid2 f2 id id) (p: lid2 = g) :
    transport (λ x, D₂ (lid1 ∘ x) _ id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ filler1 (p ▹ filler2) :=
  begin
    cases p, apply idp,
  end

  protected definition M_morphism.assoc_ur_transport {a : D₀} {lid1 lid2 f1 f2 g : hom a a}
    (filler1 : D₂ lid1 f1 id id) (filler2 : D₂ lid2 f2 id id) (p : lid1 = g) :
    transport (λ x, D₂ (x ∘ lid2) _ id id) p (comp₂ D₂ filler1 filler2)
    = comp₂ D₂ (p ▹ filler1) filler2 :=
  begin
    cases p, apply idp,
  end

  protected definition M_morphism.assoc_aux {a : D₀} (w v u : M_morphism a) :
    comp₂ D₂ (M_morphism.filler w) (M_morphism.filler (M_morphism.comp v u))
    = transport (λ x, D₂ _ (id ∘ x) id id) (id_left id)
    (comp₂ D₂ (M_morphism.filler w) (comp₂ D₂ (M_morphism.filler v)
      (M_morphism.filler u))) :=
  begin
    apply eq.inverse, apply M_morphism.assoc_bl_transport,
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
    revert r, revert p, cases q,
    intro p, cases p,
    intro r, assert P : idp = r,
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
    revert u, revert v, apply (M_morphism.rec_on w), intros [w1, w2],
    intro v, apply (M_morphism.rec_on v), intros [v1, v2],
    intro u, apply (M_morphism.rec_on u), intros [u1, u2],
    fapply M_morphism.congr,
      apply !assoc, apply concat,
      apply transport_commute,
      apply (ap (transport (λ (a_2 : hom a a), D₂ _ a_2 id id) (id_left id))),
      apply concat,
      apply (ap (transport (λ (a_3 : hom a a), D₂ a_3 (id ∘ id) id id)
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
      apply eq_tr_of_inv_tr_eq,
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
    apply (M_morphism.rec_on M), intros [lid, filler],
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
    apply (M_morphism.rec_on M), intros [lid, filler],
    fapply (M_morphism.congr),
      apply (id_right lid),
      apply concat, rotate 3, apply (id_right₂ D₂ filler),
      apply concat, apply transport_commute,
      apply (transport _ (!id_left_id_eq_id_right_id)),
      apply idp,
  end

  definition M_morphism.inv_aux ⦃a : D₀⦄ (u : M_morphism a) :
    D₂ ((M_morphism.lid u)⁻¹) id id id :=
  (@id_inverse D₀ C a (!all_iso)) ▹ (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler  u))

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
    = !id_inverse ▹
    (comp₂ D₂ (weak_dbl_gpd.inv₂ D₂ (M_morphism.filler u)) (M_morphism.filler u)) :=
  (M_morphism.inverse_compose_aux_aux u u !id_inverse)

  definition M_morphism.inverse_compose_aux4 {a : D₀} (u : M_morphism a) :=
  ap (λ x, (transport (λ (a_2 : hom a a), D₂ (ID a) a_2 id id) (id_left id)
       (transport (λ (a_3 : hom a a), D₂ a_3 (id ∘ id) id id)
          (left_inverse (M_morphism.lid u)) x)))
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
    assert p1refl : idp = p1, apply is_hset.elim, apply (transport _ p1refl),
    assert p2refl : idp = p2, apply is_hset.elim, apply (transport _ p2refl),
    apply idp,
  end

  definition M_morphism.left_inverse ⦃a : D₀⦄ (u : M_morphism a) :
    M_morphism.comp (M_morphism.inv u) u = M_morphism.one a :=
  begin
    apply (M_morphism.rec_on u), intros [lid, filler],
    fapply (M_morphism.congr),
      apply left_inverse,
      apply concat, rotate 3, apply (weak_dbl_gpd.left_inverse₂ D₂ filler),
      apply concat, apply transport_commute,
      apply concat, apply M_morphism.inverse_compose_aux4,
      apply M_morphism.inverse_compose_aux5,
  end

  protected definition M [instance] (a : D₀) : group (M_morphism a) :=
  begin
    fapply group.mk,
      intros [u, v], apply (M_morphism.comp u v),
      apply (M_morphism.is_hset a),
      intros [u, v, w], apply ((M_morphism.assoc u v w)⁻¹),
      apply M_morphism.one,
      intro u, apply (M_morphism.id_left u),
      intro u, apply (M_morphism.id_right u),
      intro u, apply (M_morphism.inv u),
      intro u, apply (M_morphism.left_inverse u),
  end

  protected definition M_bundled [reducible] (a : D₀) : Group.{l} :=
  begin
    fapply Group.mk,
      apply (M_morphism a),
    apply (M a),
  end

  end
end gamma
