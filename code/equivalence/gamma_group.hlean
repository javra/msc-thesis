import ..dbl_gpd.basic ..dbl_cat.transports ..transport4

open dbl_precat eq iso category is_trunc nat
open equiv sigma sigma.ops prod path_algebra
set_option apply.class_instance false -- disable class instance resolution in the apply tactic

set_option pp.beta true
namespace gamma
  context
  universe variables l₁ l₂ l₃
  parameters {D₀ : Type.{l₁}}
    [D₀set : is_hset D₀]
    [C : groupoid.{l₁ l₂} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type.{l₃}}
    (G : dbl_gpd C D₂)
  include G D₀set C

  structure folded_sq (a : D₀) :=
    (lid : hom a a)
    (filler : D₂ lid id id id)

  definition folded_sq.sigma_char (a : D₀) :
    (Σ (lid : hom a a), D₂ lid id id id) ≃ (folded_sq a) :=
  begin
    fapply equiv.mk,
      intro P, cases P with [lid, filler],
      exact (folded_sq.mk lid filler),
    fapply is_equiv.adjointify,
        intro P, cases P with [lid, filler], exact (⟨lid, filler⟩),
      intro P, cases P with [lid, filler], apply idp,
    intro P, cases P with [lid, filler], apply idp,
  end

  protected definition folded_sq.is_hset (a : D₀) : is_hset (folded_sq a) :=
  begin
    apply is_trunc_is_equiv_closed,
      apply equiv.to_is_equiv, apply (folded_sq.sigma_char a),
    apply is_trunc_sigma, apply !homH,
    intro f, apply (homH' G),
  end

  protected definition folded_sq.comp [reducible] {a: D₀} (v u : folded_sq a) :
    folded_sq a :=
  folded_sq.mk ((folded_sq.lid v) ∘ (folded_sq.lid u))
    (transport (λ x, D₂ ((folded_sq.lid v) ∘ (folded_sq.lid u)) x id id)
    (id_left (ID a)) (comp₂ G (folded_sq.filler v) (folded_sq.filler u)))

  protected definition folded_sq.congr ⦃a : D₀⦄
    (f1 g1 : hom a a) (f2 : D₂ f1 id id id) (g2 : D₂ g1 id id id)
    (p1 : f1 = g1) (p2 :  p1 ▹ f2 = g2) :
      folded_sq.mk f1 f2 = folded_sq.mk g1 g2 :=
  by cases p2; cases p1; apply idp

  protected definition folded_sq.congr' {a : D₀} (v u : folded_sq a)
    (p1 : folded_sq.lid v = folded_sq.lid u)
    (p2 : p1 ▹ folded_sq.filler v = folded_sq.filler u) : v = u :=
  begin
    cases v, cases u, apply folded_sq.congr, apply p2,
  end

  definition transport_commute {A B : Type} (P : A → B → Type)
    {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    {P1 : P a b} :
    p ▹ q ▹ P1 = q ▹ p ▹ P1 :=
  by cases p; cases q; apply idp

  protected definition folded_sq.assoc_aux {a : D₀} (w v u : folded_sq a) :
    comp₂ G (folded_sq.filler w) (folded_sq.filler (folded_sq.comp v u))
    = transport (λ x, D₂ _ (id ∘ x) id id) (id_left id)
    (comp₂ G (folded_sq.filler w) (comp₂ G (folded_sq.filler v)
      (folded_sq.filler u))) :=
  by apply !transp_comp₂_eq_comp₂_transp_l_b⁻¹

  protected definition folded_sq.assoc_aux2 {a : D₀} (w v u : folded_sq a) :
    comp₂ G (folded_sq.filler (folded_sq.comp w v)) (folded_sq.filler u)
    = transport (λ x, D₂ _ (x ∘ id) id id) (id_left id)
    (comp₂ G (comp₂ G (folded_sq.filler w) (folded_sq.filler v))
      (folded_sq.filler u)) :=
  by apply !transp_comp₂_eq_comp₂_transp_r_b⁻¹

  protected definition folded_sq.assoc_aux4 {a : D₀}
    {lid f f' g g' : hom a a} (filler : D₂ lid (g ∘ f) id id)
    (p : f = f') (q : g = g') (r : g ∘ f = g' ∘ f'):
    transport (λ x, D₂ lid (x ∘ f') id id) q
      (transport (λ x, D₂ lid (g ∘ x) id id) p filler)
    = transport (λ x, D₂ lid x id id) r filler :=
  begin
    cases q, cases p,
    assert P : r = idp, apply is_hset.elim,
    rewrite P,
  end

  protected definition folded_sq.assoc_aux3 {a : D₀} {lid : hom a a}
    (filler : D₂ lid (id ∘ (id ∘ id)) id id) :
    transport (λ (x : hom a a), D₂ lid (x ∘ id) id id) (inverse (id_left id))
      (transport (λ (x : hom a a), D₂ lid (id ∘ x) id id) (id_left id) filler)
    = transport (λ x, D₂ lid x id id) (assoc id id id) filler :=
  by apply folded_sq.assoc_aux4

  protected definition folded_sq.assoc ⦃a : D₀⦄ (w v u : folded_sq a) :
    folded_sq.comp w (folded_sq.comp v u) = folded_sq.comp (folded_sq.comp w v) u :=
  begin
    revert u, revert v, apply (folded_sq.rec_on w), intros [w1, w2],
    intro v, apply (folded_sq.rec_on v), intros [v1, v2],
    intro u, apply (folded_sq.rec_on u), intros [u1, u2],
    fapply folded_sq.congr,
      apply !assoc, apply concat,
      apply transport_commute,
      apply (ap (transport (λ x, D₂ _ x id id) (id_left id))),
      apply concat,
      apply (ap (transport (λ x, D₂ x (id ∘ id) id id)
       (assoc (folded_sq.lid (folded_sq.mk w1 w2)) (folded_sq.lid (folded_sq.mk v1 v2))
         (folded_sq.lid (folded_sq.mk u1 u2))))),
      apply folded_sq.assoc_aux,
      apply concat, rotate 3, apply inverse,
      apply folded_sq.assoc_aux2,
      apply concat,
      apply (transport_commute (λ x y, D₂ x (id ∘ y) id id)
        (assoc (folded_sq.lid (folded_sq.mk w1 w2))
          (folded_sq.lid (folded_sq.mk v1 v2)) (folded_sq.lid (folded_sq.mk u1 u2)))
        (id_left id)),
      apply eq_tr_of_inv_tr_eq,
      apply concat, apply folded_sq.assoc_aux3,
      apply assoc₂,
  end

  protected definition folded_sq.one [reducible] (a : D₀) : folded_sq a :=
  begin
    fapply folded_sq.mk, apply (ID a), apply (ID₂ G (ID a)),
  end

  protected definition folded_sq.id_left ⦃a : D₀⦄ (M : folded_sq a) :
    folded_sq.comp (folded_sq.one a) M = M :=
  begin
    cases M with [lid, filler],
    fapply (folded_sq.congr),
      apply (id_left lid),
      apply concat, rotate 3, apply (id_left₂ G filler),
      apply transport_commute,
  end

  definition id_left_id_eq_id_right_id ⦃ a : D₀ ⦄ : (id_left (ID a)) = (id_right (ID a)) :=
  by apply is_hset.elim

  protected definition folded_sq.id_right ⦃a : D₀⦄ (M : folded_sq a) :
    folded_sq.comp M (folded_sq.one a) = M :=
  begin
    cases M with [lid, filler],
    fapply (folded_sq.congr),
      apply (id_right lid),
      apply concat, rotate 1, apply (id_right₂ G),
      rewrite [transport_commute,-id_left_id_eq_id_right_id],
  end

  definition folded_sq.inv_aux ⦃a : D₀⦄ (u : folded_sq a) :
    D₂ ((folded_sq.lid u)⁻¹) id id id :=
  (@id_inverse D₀ C a (!all_iso)) ▹ (weak_dbl_gpd.inv₂ G (folded_sq.filler u))

  definition folded_sq.inv [reducible] ⦃a : D₀⦄ (u : folded_sq a) :
    folded_sq a :=
  begin
    fapply folded_sq.mk,
      apply ((folded_sq.lid u)⁻¹),
      exact (folded_sq.inv_aux u),
  end

  definition folded_sq.inverse_compose_aux_aux {a : D₀} (v u : folded_sq a)
    {g : hom a a} (p : id⁻¹ = g) :
  (comp₂ G (transport (λ x, D₂ ((folded_sq.lid v)⁻¹) x id id) p
    (weak_dbl_gpd.inv₂ G (folded_sq.filler v))) (folded_sq.filler u))
    = p ▹ (comp₂ G (weak_dbl_gpd.inv₂ G (folded_sq.filler v)) (folded_sq.filler u)) :=
  by cases p; apply idp

  definition folded_sq.inverse_compose_aux1 {a : D₀} (u : folded_sq a) :
    (comp₂ G (folded_sq.filler (folded_sq.inv u)) (folded_sq.filler u))
    = !id_inverse ▹
    (comp₂ G (weak_dbl_gpd.inv₂ G (folded_sq.filler u)) (folded_sq.filler u)) :=
  (folded_sq.inverse_compose_aux_aux u u !id_inverse)

  definition folded_sq.inverse_compose_aux4 {a : D₀} (u : folded_sq a) :=
  ap (λ x, (transport (λ (a_2 : hom a a), D₂ (ID a) a_2 id id) (id_left id)
       (transport (λ (a_3 : hom a a), D₂ a_3 (id ∘ id) id id)
          (left_inverse (folded_sq.lid u)) x)))
    (folded_sq.inverse_compose_aux1 u)

  definition folded_sq.inverse_compose_aux5 {a : D₀}
    {f1 f5 : hom a a} {g1 g1' g3 g4 : hom a a}
    (filler : D₂ f1 (g1 ∘ g1') (ID a) (ID a))
    (p1 : f1 = f5) (p2 : g1 ∘ g1' = g3) (p3 : g1 = g4) (p4 : f1 = f5) (p5 : g4 ∘ g1' = g3) :
    p5 ▹ p4 ▹ p3 ▹ filler
    = (transport (λ x, D₂ f5 x id id) p2
      (transport (λ x, D₂ x (g1 ∘ g1') id id) p1 filler)) :=
  begin
    cases p5, cases p4, cases p3,
    assert p1refl : p1 = idp, apply is_hset.elim,
    assert p2refl : p2 = idp, apply is_hset.elim,
    rewrite [p2refl, p1refl],
  end

  definition folded_sq.left_inverse ⦃a : D₀⦄ (u : folded_sq a) :
    folded_sq.comp (folded_sq.inv u) u = folded_sq.one a :=
  begin
    cases u with [lid, filler],
    fapply (folded_sq.congr),
      apply left_inverse,
      apply concat, rotate 1, apply (weak_dbl_gpd.left_inverse₂ G filler),
      apply concat, apply transport_commute,
      apply concat, apply folded_sq.inverse_compose_aux4,
      apply folded_sq.inverse_compose_aux5,
  end

  protected definition folded_sq_group [instance] (a : D₀) : group (folded_sq a) :=
  begin
    fapply group.mk,
      intros [u, v], apply (folded_sq.comp u v),
      apply (folded_sq.is_hset a),
      intros [u, v, w], apply ((folded_sq.assoc u v w)⁻¹),
      apply folded_sq.one,
      intro u, apply (folded_sq.id_left u),
      intro u, apply (folded_sq.id_right u),
      intro u, apply (folded_sq.inv u),
      intro u, apply (folded_sq.left_inverse u),
  end

  protected definition folded_sq_Group [reducible] (a : D₀) : Group.{max l₂ l₃} :=
  Group.mk (folded_sq a) (folded_sq_group a)

  end
end gamma
