import .gamma_group ..transport4 ..dbl_gpd.basic ..dbl_cat.transports

open dbl_precat eq iso category is_trunc nat
open equiv sigma sigma.ops prod
open algebra dbl_gpd
attribute gamma.folded_sq_group [instance]

set_option pp.beta true
namespace gamma
  section
  --universe variable l
  parameters {D₀ : Type/-.{l}-/}
    [D₀set : is_hset D₀]
    [C : groupoid/-.{l l}-/ D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type/-.{l}-/}
    (G : dbl_gpd C D₂)
  include G D₀set C

  attribute dbl_gpd.T [instance]

  protected definition mu [reducible] ⦃x : D₀⦄ (u : folded_sq G x) : hom x x :=
  folded_sq.lid u

  protected definition mu_respect_comp ⦃x : D₀⦄ (v u : folded_sq G x) :
    mu (v * u) = mu v ∘ mu u :=
  idp

  protected definition mu_respect_id ⦃x : D₀⦄ : mu 1 = ID x :=
  idp

  protected definition phi [reducible] ⦃x y : D₀⦄ (a : hom x y) (u : folded_sq G x) :
    folded_sq G y :=
  begin
    fapply folded_sq.mk,
      apply (a ∘ (folded_sq.lid u) ∘ a⁻¹),
    assert v : D₂ (a ∘ (folded_sq.lid u) ∘ a⁻¹) (a ∘ id ∘ a⁻¹) id id,
      apply (comp₂ G (dbl_precat.ID₁ G a) (comp₂ G (folded_sq.filler u) (dbl_precat.ID₁ G (a⁻¹)))),
    exact (transport (λ x, D₂ _ x id id) (right_inverse a)
             (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (a⁻¹)) v)),
  end

  protected definition phi_respect_id_aux ⦃y : D₀⦄ {lid bottom : hom y y}
    (filler : D₂ lid bottom id id) :
    comp₂ G (ID₂ G (ID y)) filler
    = transport (λ x, D₂ x _ id id) ((id_left lid)⁻¹)
      (transport (λ x, D₂ lid x id id) ((id_left bottom)⁻¹) filler) :=
  begin
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply id_left₂,
  end

  protected definition phi_respect_id_aux2 ⦃y : D₀⦄ {lid bottom : hom y y}
    (filler : D₂ lid bottom id id) :
    comp₂ G filler (ID₂ G (ID y))
    = transport (λ x, D₂ x _ id id) ((id_right lid)⁻¹)
      (transport (λ x, D₂ lid x id id) ((id_right bottom)⁻¹) filler) :=
  begin
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply id_right₂,
  end

  protected definition phi_respect_id ⦃y : D₀⦄ (u : folded_sq G y) :
    phi (ID y) u = u :=
  begin
    apply (folded_sq.rec_on u), intros [lid, filler],
    fapply folded_sq.congr,
      apply concat, apply id_left,
      apply concat, apply (ap (λ x, _ ∘ x)),
      apply id_inverse,
      apply id_right,
    do 3 apply tr_eq_of_eq_inv_tr,
    apply (transport (λ x, comp₂ G x _ = _) (zero_unique G y)⁻¹),
    apply concat, apply phi_respect_id_aux,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat,  apply (eq_inv_tr_of_tr_eq
      (apd (λ x, comp₂ G filler (ID₁ G x)) (!id_inverse))),
    apply inv_tr_eq_of_eq_tr,
    apply (transport (λ x, comp₂ G _ x = _) (zero_unique G y)⁻¹),
    apply concat, apply phi_respect_id_aux2,
    do 2 apply inv_tr_eq_of_eq_tr, apply inverse,
    apply concat,
    apply (@transport_eq_transport4 _ _ _ _ (@D₂ y y y y) (hom y y)
      (λ x, lid) (λ x, x) (λ x, id) (λ x, id) _ _ (id_right id)),
    do 7 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce
  end

  protected definition phi_respect_P_comp₂_aux ⦃x y z : D₀⦄ (a : hom x y)
    (f1 : hom y x) (f2 : hom y y)
    (b : hom y z) (lid : hom x x) (filler : D₂ lid id id id)
    (p : id ∘ (a⁻¹) = f1) (q : a ∘ f1 = f2) :
  comp₂ G (ID₁ G b)
    (comp₂ G
         (transport (λ x, D₂ (a ∘ lid ∘ (a⁻¹)) x id id) q
             (transport (λ x, D₂ (a ∘ lid ∘ (a⁻¹)) (a ∘ x) id id) p
          (comp₂ G (ID₁ G a) (comp₂ G filler (ID₁ G (a⁻¹))))))
       (ID₁ G (b⁻¹)))
  = transport (λ x, D₂ (b ∘ (a ∘ lid ∘ (a⁻¹)) ∘ (b⁻¹)) (b ∘ x ∘ (b⁻¹)) id id) q
      (transport (λ x, D₂ (b ∘ (a ∘ lid ∘ (a⁻¹)) ∘ (b⁻¹)) (b ∘ (a ∘ x) ∘ (b⁻¹)) id id) p
        (comp₂ G (ID₁ G b) (comp₂ G
          (comp₂ G (ID₁ G a) (comp₂ G filler (ID₁ G (a⁻¹))))
          (ID₁ G (b⁻¹))))) :=
  begin
    cases q, cases p, esimp,
  end

  protected definition Pbainv ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z) :
    (a⁻¹) ∘ (b⁻¹) = (b ∘ a)⁻¹ :=
  ((@iso.comp_inverse _ _ _ _ _ b a (!all_iso) (!all_iso) (!all_iso))⁻¹)

  protected definition phi_respect_P_comp₂_aux2 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :
    comp₂ G (comp₂ G (ID₁ G b) (ID₁ G a))
    (comp₂ G filler
       ((Pbainv a b) ▸ comp₂ G (ID₁ G (a⁻¹)) (ID₁ G (b⁻¹)))) =
    transport _
      (Pbainv a b)
      (comp₂ G (comp₂ G (ID₁ G b) (ID₁ G a))
        (comp₂ G filler
          (comp₂ G (ID₁ G (a⁻¹)) (ID₁ G (b⁻¹))))) :=
  begin
    apply (eq.rec_on (Pbainv a b)), apply idp,
  end

  protected definition phi_respect_P_comp₂_aux3 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  ap (λ x, comp₂ G (ID₁ G b)
    (comp₂ G (ID₁ G a) x))
    (eq_inv_tr_of_tr_eq
    (eq_inv_tr_of_tr_eq (assoc₂ G filler (ID₁ G a⁻¹) (ID₁ G b⁻¹))))

  protected definition phi_respect_P_comp₂_aux4 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (f1 f2 g1 g2 : hom z x) (filler : D₂ f1 f2 id id) (p : f1 = g1) (q : f2 = g2) :
    transport (λ x, D₂ (b ∘ (a ∘ x)) _ id id) p
      (transport (λ x, D₂ _ (b ∘ (a ∘ x)) id id) q
        (comp₂ G (ID₁ G b) (comp₂ G (ID₁ G a)
          filler)))
   = (comp₂ G (ID₁ G b) (comp₂ G (ID₁ G a)
        (transport (λ x, D₂ x _ id id) p
          (transport (λ x, D₂ _ x id id) q
            filler)))) :=
  begin
    cases q, cases p, esimp,
  end

  protected definition phi_respect_P_comp₂_aux5 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  ap (λ x, comp₂ G (ID₁ G b) x)
    (eq_inv_tr_of_tr_eq
      (eq_inv_tr_of_tr_eq
        (assoc₂ G (ID₁ G a) (comp₂ G filler (ID₁ G a⁻¹)) (ID₁ G b⁻¹))))

  protected definition phi_respect_P_comp₂_aux7 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  transp_comp₂_eq_comp₂_transp_l_bu G
    (comp₂ G (comp₂ G (ID₁ G a)
      (comp₂ G filler (ID₁ G a⁻¹))) (ID₁ G b⁻¹))
    ((assoc a (lid ∘ a⁻¹) b⁻¹)⁻¹)
    ((assoc a (id ∘ a⁻¹) b⁻¹)⁻¹) (dbl_precat.ID₁ G b)

  set_option unifier.max_steps 50000
  protected definition phi_respect_P_comp ⦃x y z : D₀⦄ (b : hom y z) (a : hom x y)
    (u : folded_sq G x) : phi (b ∘ a) u = phi b (phi a u) :=
  begin
    cases u with [lid, filler],
    fapply folded_sq.congr,
      apply (transport _ (Pbainv a b)),
      apply concat, apply inverse, apply assoc, apply (ap (λ x, b ∘ x)),
      do 2 (apply concat; apply assoc),
      apply (ap (λ x, x ∘ b⁻¹)), esimp[gamma.phi],
      apply inverse, apply assoc,
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply inverse, apply concat, apply phi_respect_P_comp₂_aux,
    do 2 apply eq_inv_tr_of_tr_eq, do 3 apply eq_tr_of_inv_tr_eq,
    assert P1 : ID₁ G (b ∘ a) = comp₂ G (ID₁ G b) (ID₁ G a),
      apply (id_comp₂ G),
    apply (transport (λ x, _ = comp₂ G x _) P1⁻¹),
    apply concat, rotate 3, apply inverse,
    assert P2 : ID₁ G (b ∘ a)⁻¹ʰ
      = (Pbainv a b) ▸ ID₁ G ((a⁻¹ʰ) ∘ (b⁻¹ʰ)),
      apply (eq.rec_on (Pbainv a b)), apply idp,
    apply (ap (λ x, comp₂ G (comp₂ G (ID₁ G b) (ID₁ G a))
      (comp₂ G filler x)) P2),
    assert P4 : ID₁ G (a⁻¹ʰ ∘ b⁻¹ʰ) = comp₂ G (ID₁ G a⁻¹ʰ) (ID₁ G b⁻¹ʰ),
      apply (id_comp₂ G),
    apply (transport (λ x, _ = comp₂ G _ (comp₂ G filler ((Pbainv a b) ▸ x))) P4⁻¹),
    apply concat, rotate 1, apply inverse, apply phi_respect_P_comp₂_aux2,
    apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 1, apply (assoc₂ G),
    do 2 apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 1, apply inverse, apply phi_respect_P_comp₂_aux3,
    apply concat, rotate 1, apply phi_respect_P_comp₂_aux4,
    do 2 apply eq_inv_tr_of_tr_eq,
    apply concat, rotate 1, apply inverse, apply phi_respect_P_comp₂_aux5,
    apply concat, rotate 1, apply phi_respect_P_comp₂_aux7,
    do 2 apply eq_inv_tr_of_tr_eq,
    apply concat,
    apply (@transport_eq_transport4 (hom z z) (hom z z) (hom z z) (hom z z)
          (@D₂ z z z z) (hom z y)
          (λ w, (b ∘ ((a ∘ (lid ∘ a⁻¹)) ∘ b⁻¹)))
          (λ w, b ∘ w) (λ w, id) (λ w, id) _ _ (assoc a (id ∘ a⁻¹) b⁻¹)),
    do 13 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

  protected definition phi_respect_M_comp₂_aux ⦃x y : D₀⦄ (a : hom x y)
    (lidv lidu : hom x x) (fillerv : D₂ lidv id id id) (filleru : D₂ lidu id id id) :
  comp₂ G
    (transport (λ x, D₂ _ x id id) (@right_inverse D₀ C x y a (!all_iso))
      (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (@iso.inverse D₀ C _ _ a (!all_iso)))
         (comp₂ G (ID₁ G a) (comp₂ G fillerv (ID₁ G (@iso.inverse D₀ C _ _ a (!all_iso)))))))
    (transport (λ x, D₂ _ x id id) (@right_inverse D₀ C x y a (!all_iso))
      (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (@iso.inverse D₀ C _ _ a (!all_iso)))
        (comp₂ G (ID₁ G a) (comp₂ G filleru (ID₁ G (@iso.inverse D₀ C _ _ a (!all_iso)))))))
  = (transport (λ x, D₂ _ (x ∘ _) id id) (@right_inverse D₀ C x y a (!all_iso))
      (transport (λ x, D₂ _ ((a ∘ x) ∘ _) id id) (id_left (@iso.inverse D₀ C _ _ a (!all_iso)))
        (transport (λ x, D₂ _ (_ ∘ x) id id) (@right_inverse D₀ C x y a (!all_iso))
          (transport (λ x, D₂ _ (_ ∘ (a ∘ x)) id id) (id_left (@iso.inverse D₀ C _ _ a (!all_iso)))
            (comp₂ G
              (comp₂ G (ID₁ G a) (comp₂ G fillerv (ID₁ G (@iso.inverse D₀ C _ _ a (!all_iso)))))
              (comp₂ G (ID₁ G a) (comp₂ G filleru (ID₁ G (@iso.inverse D₀ C _ _ a (!all_iso)))))))))) :=
  begin
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b G),
    apply (ap (λ x, transport _ _ x)),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b G),
    apply (ap (λ x, transport _ _ x)),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b G),
    apply (ap (λ x, transport _ _ x)),
    apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b G),
  end

  protected definition phi_respect_M_comp₂_aux2 ⦃x y: D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  ap (λ x, comp₂ G x (comp₂ G filleru (ID₁ G (a⁻¹))))
  (assoc₂ G (ID₁ G a) (comp₂ G fillerv (ID₁ G (a⁻¹))) (ID₁ G a))⁻¹

  protected definition phi_respect_M_comp₂_aux3 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  ap (λ x, comp₂ G (comp₂ G (ID₁ G a) x) (comp₂ G filleru (ID₁ G (a⁻¹))))
  ((assoc₂ G fillerv (ID₁ G (a⁻¹)) (ID₁ G a))⁻¹)

  protected definition phi_respect_M_comp₂_aux4 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  (ap (λ w, comp₂ G (comp₂ G (ID₁ G a) (comp₂ G fillerv w)) (comp₂ G filleru (ID₁ G (a⁻¹))))
  (ID₁_inverse_compose G a))

  protected definition phi_respect_M_comp₂_aux5 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  (ap (λ w, comp₂ G (comp₂ G (ID₁ G a) (comp₂ G fillerv w)) (comp₂ G filleru (ID₁ G (a⁻¹))))
    (zero_unique G x))

  protected definition phi_respect_M_comp ⦃x y : D₀⦄ (a : hom x y) (v u : folded_sq G x) :
    phi a (folded_sq.comp G v u) = folded_sq.comp G (phi a v) (phi a u) :=
  begin
    cases v with [lidv, fillerv],
    cases u with [lidu, filleru],
    --Part I : Equality of lids
    fapply (folded_sq.congr),
      apply concat, rotate 4, apply inverse,
      apply (!assoc⁻¹), rotate 3, apply (ap (λ x, a ∘ x)),
      apply concat,  rotate 4, apply inverse,
      apply (!assoc⁻¹), rotate 3,
      apply concat, apply (!assoc⁻¹), apply (ap (λ x, lidv ∘ x)),
      apply concat, rotate 4, apply inverse, apply assoc, rotate 3,
      apply concat, rotate 4, apply inverse, apply assoc, rotate 3, apply (ap (λ x, x ∘ a⁻¹)),
      apply concat, apply (!id_left⁻¹), apply (ap (λ x, x ∘ lidu)),
      apply inverse, apply left_inverse,
    --Part II: Equality of fillers
    do 3 apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ G (ID₁ G a) x)),
    apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_ub G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_ub G),
    do 3 apply eq_inv_tr_of_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 3, apply inverse, apply phi_respect_M_comp₂_aux,
    do 2 apply eq_tr_of_inv_tr_eq, do 2 apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 3, apply inverse, apply (assoc₂' G),
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply concat, rotate 3, apply inverse, apply phi_respect_M_comp₂_aux2,
    apply concat, rotate 3, apply (transp_comp₂_eq_comp₂_transp_r_ub G),
    do 2 apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 3, apply inverse, apply phi_respect_M_comp₂_aux3,
    apply concat, rotate 3, apply (ap (λ x, comp₂ G x _)),
    apply (transp_comp₂_eq_comp₂_transp_l_ub G),
    apply concat, rotate 3, apply (transp_comp₂_eq_comp₂_transp_r_ub G),
    do 2 apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 3, apply inverse, apply phi_respect_M_comp₂_aux4,
    apply concat, rotate 3, apply (ap (λ x, comp₂ G (comp₂ G (ID₁ G a) x) _)),
    apply (transp_comp₂_eq_comp₂_transp_l_ub G),
    apply concat, rotate 3, apply (ap (λ x, comp₂ G x _)),
    apply (transp_comp₂_eq_comp₂_transp_l_ub G),
    apply concat, rotate 3, apply (transp_comp₂_eq_comp₂_transp_r_ub G),
    do 2 apply eq_inv_tr_of_tr_eq,
    apply concat, rotate 3, apply inverse, apply phi_respect_M_comp₂_aux5,
    apply concat, rotate 3,
    apply (ap (λ x, comp₂ G (comp₂ G (ID₁ G a) x) _)),
    apply inverse, apply (id_right₂' G fillerv),
    apply concat, rotate 3, apply (ap (λ x, comp₂ G x _)),
    apply (transp_comp₂_eq_comp₂_transp_l_bu G),
    apply concat, rotate 3, apply (transp_comp₂_eq_comp₂_transp_r_bu G),
    do 2 apply eq_inv_tr_of_tr_eq,
    apply concat, rotate 3, apply (assoc₂ G),
    do 2 apply eq_tr_of_inv_tr_eq,
    apply concat, rotate 3, apply inverse, apply (ap (λ x, comp₂ G _ x)),
    apply (assoc₂' G),
    apply concat, rotate 3, apply (transp_comp₂_eq_comp₂_transp_l_bu G),
    do 2 apply eq_inv_tr_of_tr_eq,
    apply concat,
    apply (@transport_eq_transport4 (hom y y) (hom y y) (hom y y) (hom y y)
      (@D₂ y y y y) (hom y x)
      (λ w, (a ∘ ((lidv ∘ lidu) ∘ _)))
      (λ w, a ∘ w) (λ w, id) (λ w, id) _ _ (assoc id id _)),
    do 25 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce, repeat ( apply homH ),
  end

  end
end gamma
