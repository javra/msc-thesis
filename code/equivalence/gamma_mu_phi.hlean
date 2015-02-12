import .gamma_group ..transport4 ..dbl_gpd.basic ..dbl_cat.transports

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod
open path_algebra dbl_gpd
attribute gamma.M [instance]

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

  attribute dbl_gpd.T [instance]

  protected definition mu [reducible] ⦃x : D₀⦄ (u : M_morphism x) : hom x x :=
  M_morphism.lid u

  protected definition mu_respect_comp ⦃x : D₀⦄ (v u : M_morphism x) :
    mu (v * u) = mu v ∘ mu u :=
  idp

  protected definition mu_respect_id ⦃x : D₀⦄ : mu 1 = ID x :=
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
    {lid f2 f3 g0 g1 g2 g3 g4 g5 g6 g7 : hom y y}
    (p8 : lid = f2) (p7 : g0 = g1 ∘ g2) (p6 : g2 = @comp D₀ C y y y g3 g4)
    (p5 : f2 = f3 ∘ g6) (p4 : g1 ∘ (g3 ∘ g4) = g5 ∘ g6)
    (p3 : g6 = g7) (p2 : f3 ∘ g7 = lid) (p1 : g5 ∘ g7 = g0)
    (filler : D₂ lid g0 id id)

  protected definition phi_respect_id ⦃y : D₀⦄ (u : M_morphism y) :
    phi (ID y) u = u :=
  begin
    apply (M_morphism.rec_on u), intros (lid, filler),
    fapply (M_morphism.congr),
      apply concat, apply id_left,
      apply concat, apply (ap (λ x, _ ∘ x)),
      apply (@iso_of_id' D₀ D₀set C D₂ G),
      apply id_right,
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    apply (transport (λ x, comp₂ D₂ x _ = _) ((zero_unique D₂ y)⁻¹)),
    apply concat, apply phi_respect_id_aux,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat,  apply (moveL_transport_V _ _ _ _
      (apD (λ x, comp₂ D₂ filler (ID₁ D₂ x)) (@iso_of_id' D₀ D₀set C D₂ G y))),
    apply moveR_transport_V,
    apply (transport (λ x, comp₂ D₂ _ x = _) ((zero_unique D₂ y)⁻¹)),
    apply concat, apply phi_respect_id_aux2,
    apply moveR_transport_V, apply moveR_transport_V, apply inverse,
    apply concat,
    apply (@transport_eq_transport4 _ _ _ _ (@D₂ y y y y) (hom y y)
      (λ x, lid) (λ x, x) (λ x, id) (λ x, id) _ _ (id_right id)),
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply transport4_set_reduce
  end

  protected definition inv_pp' ⦃x y z : D₀⦄ (b : hom y z) (a : hom x y) :
    (@morphism.inverse D₀ C x z (b ∘ a) (!all_iso)) = (a⁻¹) ∘ (b⁻¹):=
  have H1 : (a⁻¹ ∘ b⁻¹) ∘ b ∘ a = a⁻¹ ∘ (b⁻¹ ∘ (b ∘ a)), from assoc (a⁻¹) (b⁻¹) (b ∘ a)⁻¹,
  have H2 : (a⁻¹) ∘ (b⁻¹ ∘ (b ∘ a)) = a⁻¹ ∘ a, from ap _ (iso.compose_V_pp b a),
  have H3 : a⁻¹ ∘ a = id, from inverse_compose a,
  sorry --inverse_eq_intro_left (H1 ⬝ H2 ⬝ H3)

  set_option unifier.max_steps 50000
  protected definition phi_respect_P_comp₂_aux ⦃x y z : D₀⦄ (a : hom x y)
    (f1 : hom y x) (f2 : hom y y)
    (b : hom y z) (lid : hom x x) (filler : D₂ lid id id id)
    (p : id ∘ (a⁻¹) = f1) (q : a ∘ f1 = f2) :
  comp₂ D₂ (ID₁ D₂ b)
    (comp₂ D₂
         (transport (λ x, D₂ (a ∘ lid ∘ (a⁻¹)) x id id) q
             (transport (λ x, D₂ (a ∘ lid ∘ (a⁻¹)) (a ∘ x) id id) p
          (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ filler (ID₁ D₂ (a⁻¹))))))
       (ID₁ D₂ (b⁻¹)))
  = transport (λ x, D₂ (b ∘ (a ∘ lid ∘ (a⁻¹)) ∘ (b⁻¹)) (b ∘ x ∘ (b⁻¹)) id id) q
      (transport (λ x, D₂ (b ∘ (a ∘ lid ∘ (a⁻¹)) ∘ (b⁻¹)) (b ∘ (a ∘ x) ∘ (b⁻¹)) id id) p
        (comp₂ D₂ (ID₁ D₂ b) (comp₂ D₂
          (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ filler (ID₁ D₂ (a⁻¹))))
          (ID₁ D₂ (b⁻¹))))) :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  protected definition Pbainv ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z) :
    (a⁻¹) ∘ (b⁻¹) = (@morphism.inverse D₀ C x z (b ∘ a) (!all_iso)) :=
  ((inv_pp' b a)⁻¹)

  protected definition phi_respect_P_comp₂_aux2 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :
    comp₂ D₂ (comp₂ D₂ (ID₁ D₂ b) (ID₁ D₂ a))
    (comp₂ D₂ filler
       ((Pbainv a b) ▹ comp₂ D₂ (ID₁ D₂ (a⁻¹)) (ID₁ D₂ (b⁻¹)))) =
    transport _
      (Pbainv a b)
      (comp₂ D₂ (comp₂ D₂ (ID₁ D₂ b) (ID₁ D₂ a))
        (comp₂ D₂ filler
          (comp₂ D₂ (ID₁ D₂ (a⁻¹)) (ID₁ D₂ (b⁻¹))))) :=
  begin
    apply (eq.rec_on (Pbainv a b)), apply idp,
  end

  protected definition phi_respect_P_comp₂_aux3 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  ap (λ x, comp₂ D₂ (ID₁ D₂ b)
    (comp₂ D₂ (ID₁ D₂ a) x))
    (moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (assoc₂ D₂ filler (ID₁ D₂ (a⁻¹)) (ID₁ D₂ (b⁻¹)))))

  protected definition phi_respect_P_comp₂_aux4 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (f1 f2 g1 g2 : hom z x) (filler : D₂ f1 f2 id id) (p : f1 = g1) (q : f2 = g2) :
    transport (λ x, D₂ (b ∘ (a ∘ x)) _ id id) p
      (transport (λ x, D₂ _ (b ∘ (a ∘ x)) id id) q
        (comp₂ D₂ (ID₁ D₂ b) (comp₂ D₂ (ID₁ D₂ a)
          filler)))
   = (comp₂ D₂ (ID₁ D₂ b) (comp₂ D₂ (ID₁ D₂ a)
        (transport (λ x, D₂ x _ id id) p
          (transport (λ x, D₂ _ x id id) q
            filler)))) :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  protected definition phi_respect_P_comp₂_aux5 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  ap (λ x, comp₂ D₂ (ID₁ D₂ b) x)
    (moveL_transport_V _ _ _ _
      (moveL_transport_V _ _ _ _
        (assoc₂ D₂ (ID₁ D₂ a) (comp₂ D₂ filler (ID₁ D₂ (a⁻¹))) (ID₁ D₂ (b⁻¹)))))

  protected definition phi_respect_P_comp₂_aux7 ⦃x y z : D₀⦄ (a : hom x y) (b : hom y z)
    (lid : hom x x) (filler : D₂ lid id id id) :=
  transp_comp₂_eq_comp₂_transp_l_bu
    (comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a)
      (comp₂ D₂ filler (ID₁ D₂ (a⁻¹)))) (ID₁ D₂ (b⁻¹)))
    ((assoc a (lid ∘ (a⁻¹)) (b⁻¹))⁻¹)
    ((assoc a (id ∘ (a⁻¹)) (b⁻¹))⁻¹) (ID₁ D₂ b)

  set_option unifier.max_steps 40000
  protected definition phi_respect_P_comp ⦃x y z : D₀⦄ (b : hom y z) (a : hom x y)
    (u : M_morphism x) : phi (b ∘ a) u = phi b (phi a u) :=
  begin
    assert (bainv : hom z x),
      exact (@morphism.inverse D₀ C x z (b ∘ a) (!all_iso)),
    apply (M_morphism.rec_on u), intros (lid, filler),
    fapply (M_morphism.congr),
      apply (transport _ (Pbainv a b)),
      apply concat, apply (!assoc⁻¹), apply (ap (λ x, b ∘ x)),
      apply concat, rotate 3, apply assoc,
      apply concat, rotate 3, apply assoc, apply (ap (λ x, x ∘ (b⁻¹))),
      apply concat, rotate 3, apply (!assoc⁻¹), apply (ap (λ x, a ∘ x)),
      apply (ap (λ x, x ∘ (a⁻¹))), apply idp,
    apply moveL_transport_p, apply moveL_transport_p,
    apply inverse,
    apply concat,
    apply phi_respect_P_comp₂_aux,
    apply moveL_transport_V, apply moveL_transport_V, apply moveL_transport_p,
    apply moveL_transport_p, apply moveL_transport_p,
    assert (P1 : ID₁ D₂ (b ∘ a) = comp₂ D₂ (ID₁ D₂ b) (ID₁ D₂ a)),
      apply id_comp₂,
    apply (transport (λ x, _ = comp₂ D₂ x _) (P1⁻¹)),
    apply concat, rotate 3, apply inverse,
    assert (P2 : ID₁ D₂ (@morphism.inverse D₀ C x z (b ∘ a) (!all_iso))
      = (Pbainv a b) ▹ ID₁ D₂ ((a⁻¹) ∘ (b⁻¹))),
      apply (eq.rec_on (Pbainv a b)), apply idp,
    apply (ap (λ x, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ b) (ID₁ D₂ a))
      (comp₂ D₂ filler x)) P2),
    assert (P4 : ID₁ D₂ (a⁻¹ ∘ b⁻¹) = comp₂ D₂ (ID₁ D₂ (a⁻¹)) (ID₁ D₂ (b⁻¹))),
      apply id_comp₂,
    apply (transport (λ x, _ = comp₂ D₂ _ (comp₂ D₂ filler ((Pbainv a b) ▹ x))) (P4⁻¹)),
    apply concat, rotate 3, apply inverse, apply phi_respect_P_comp₂_aux2,
    apply moveL_transport_p,
    apply concat, rotate 3, apply assoc₂,
    apply moveL_transport_p, apply moveL_transport_p,
    apply concat, rotate 3, apply inverse, apply phi_respect_P_comp₂_aux3,
    apply concat, rotate 3, apply phi_respect_P_comp₂_aux4,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat, rotate 3, apply inverse, apply phi_respect_P_comp₂_aux5,
    apply concat, rotate 3, apply phi_respect_P_comp₂_aux7,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat,
    apply (@transport_eq_transport4 (hom z z) (hom z z) (hom z z) (hom z z)
          (@D₂ z z z z) (hom z y)
          (λ w, (b ∘ ((a ∘ (lid ∘ (a⁻¹))) ∘ (b⁻¹))))
          (λ w, b ∘ w) (λ w, id) (λ w, id) _ _ (assoc a (id ∘ (a⁻¹)) (b⁻¹))),
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply transport4_set_reduce,
  end

  --set_option pp.implicit true
  --set_option pp.notation false

  protected definition phi_respect_M_comp₂_aux ⦃x y : D₀⦄ (a : hom x y)
    (lidv lidu : hom x x) (fillerv : D₂ lidv id id id) (filleru : D₂ lidu id id id) :
  comp₂ D₂
    (transport (λ x, D₂ _ x id id) (compose_inverse a)
      (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (a⁻¹))
         (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ fillerv (ID₁ D₂ (a⁻¹))))))
    (transport (λ x, D₂ _ x id id) (compose_inverse a)
      (transport (λ x, D₂ _ (a ∘ x) id id) (id_left (a⁻¹))
        (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))))
  = (transport (λ x, D₂ _ (x ∘ _) id id) (compose_inverse a)
      (transport (λ x, D₂ _ ((a ∘ x) ∘ _) id id) (id_left (a⁻¹))
        (transport (λ x, D₂ _ (_ ∘ x) id id) (compose_inverse a)
          (transport (λ x, D₂ _ (_ ∘ (a ∘ x)) id id) (id_left (a⁻¹))
            (comp₂ D₂
              (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ fillerv (ID₁ D₂ (a⁻¹))))
              (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))))))) :=
  begin
    /-generalize (compose_inverse a), intro ci,
    generalize (id_left (a⁻¹)),
    apply (eq.rec_on ci),-/
    exact sorry,
  end

  protected definition assoc₂' ⦃a b c₁ d₁ c₂ d₂ c₃ d₃ : D₀⦄
    ⦃f  : hom a b⦄   ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    ⦃g₃ : hom c₃ d₃⦄ ⦃h₃ : hom c₂ c₃⦄ ⦃i₃ : hom d₂ d₃⦄
    (w : D₂ h₃ i₃ g₂ g₃) (v : D₂ h₂ i₂ g₁ g₂) (u : D₂ h₁ i₁ f g₁) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (assoc₂ D₂ w v u))

  protected definition id_left₂' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (id_left₂ D₂ u))

  protected definition id_right₂' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (id_right₂ D₂ u))

  protected definition id_left₁' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (id_left₁ D₂ u))

  protected definition id_right₁' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (id_right₁ D₂ u))

  protected definition phi_respect_M_comp₂_aux2 ⦃x y: D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  ap (λ x, comp₂ D₂ x (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))
  (assoc₂ D₂ (ID₁ D₂ a) (comp₂ D₂ fillerv (ID₁ D₂ (a⁻¹))) (ID₁ D₂ a))⁻¹

  protected definition phi_respect_M_comp₂_aux3 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  ap (λ x, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a) x) (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))
  ((assoc₂ D₂ fillerv (ID₁ D₂ (a⁻¹)) (ID₁ D₂ a))⁻¹)

  protected definition phi_respect_M_comp₂_aux4 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  (ap (λ w, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ fillerv w)) (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))
  (ID₁_inverse_compose a))

  protected definition phi_respect_M_comp₂_aux5 ⦃x y : D₀⦄ {a : hom x y} (lidu : hom x x)
    (filleru : D₂ lidu id id id) (lidv : hom x x) (fillerv : D₂ lidv id id id) :=
  (ap (λ w, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ fillerv w)) (comp₂ D₂ filleru (ID₁ D₂ (a⁻¹))))
    (zero_unique D₂ x))

  --set_option pp.implicit true
  --set_option pp.notation false
  protected definition phi_respect_M_comp ⦃x y : D₀⦄ (a : hom x y) (v u : M_morphism x) :
    phi a (M_morphism.comp v u) = M_morphism.comp (phi a v) (phi a u) :=
  begin
    apply (M_morphism.rec_on v), intros (lidv, fillerv),
    apply (M_morphism.rec_on u), intros (lidu, filleru),
    --Part I : Equality of lids
    fapply (M_morphism.congr), --unfold gamma.phi,
      apply concat, rotate 1, apply inverse,
      apply (!assoc⁻¹), rotate 1, apply (ap (λ x, a ∘ x)),
      apply concat,  rotate 1, apply inverse,
      apply (!assoc⁻¹), rotate 1,
      apply concat, apply (!assoc⁻¹), apply (ap (λ x, lidv ∘ x)),
      apply concat, rotate 1, apply inverse, apply assoc, rotate 1,
      apply concat, rotate 1, apply inverse, apply assoc, rotate 1, apply (ap (λ x, x ∘ a⁻¹)),
      apply concat, apply (!id_left⁻¹), apply (ap (λ x, x ∘ lidu)),
      apply inverse, apply inverse_compose,
    --Part II: Equality of fillers
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    apply concat, apply (ap (λ x, comp₂ D₂ (ID₁ D₂ a) x)),
    apply inverse, apply transp_comp₂_eq_comp₂_transp_r_ub,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub,
    apply moveL_transport_V, apply moveL_transport_V, apply moveL_transport_V,
    apply moveL_transport_p,
    apply concat, rotate 1, apply inverse, apply phi_respect_M_comp₂_aux,
    apply moveL_transport_p, apply moveL_transport_p,
    apply moveL_transport_p, apply moveL_transport_p,
    apply concat, rotate 1, apply inverse, apply assoc₂',
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat, rotate 1, apply inverse, apply phi_respect_M_comp₂_aux2,
    --apply (apD (λ x, comp₂ D₂ x (comp₂ D₂ filleru (ID₁ D₂ a ⁻¹)))),
    apply concat, rotate 1, apply transp_comp₂_eq_comp₂_transp_r_ub,
    apply moveL_transport_p, apply moveL_transport_p,
    apply concat, rotate 1, apply inverse, apply phi_respect_M_comp₂_aux3,
    apply concat, rotate 1, apply (ap (λ x, comp₂ D₂ x _)),
    apply transp_comp₂_eq_comp₂_transp_l_ub,
    apply concat, rotate 1, apply transp_comp₂_eq_comp₂_transp_r_ub,
    apply moveL_transport_p, apply moveL_transport_p,
    apply concat, rotate 1, apply inverse, apply phi_respect_M_comp₂_aux4,
    apply concat, rotate 1, apply (ap (λ x, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a) x) _)),
    apply transp_comp₂_eq_comp₂_transp_l_ub,
    apply concat, rotate 1, apply (ap (λ x, comp₂ D₂ x _)),
    apply transp_comp₂_eq_comp₂_transp_l_ub,
    apply concat, rotate 1, apply transp_comp₂_eq_comp₂_transp_r_ub,
    apply moveL_transport_V, apply moveL_transport_V, beta,
    apply concat, rotate 1, apply inverse, apply phi_respect_M_comp₂_aux5,
    apply concat, rotate 1,
    apply (ap (λ x, comp₂ D₂ (comp₂ D₂ (ID₁ D₂ a) x) _)),
    apply inverse, apply (id_right₂' fillerv),
    apply concat, rotate 1, apply (ap (λ x, comp₂ D₂ x _)),
    apply transp_comp₂_eq_comp₂_transp_l_bu,
    apply concat, rotate 1, apply transp_comp₂_eq_comp₂_transp_r_bu,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat, rotate 1, apply inverse, apply (!assoc₂⁻¹),
    apply moveL_transport_p, apply moveL_transport_p,
    apply concat, rotate 1, apply inverse, apply (ap (λ x, comp₂ D₂ _ x)),
    apply assoc₂',
    apply concat, rotate 1, apply transp_comp₂_eq_comp₂_transp_l_bu,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat,
    apply (@transport_eq_transport4 (hom y y) (hom y y) (hom y y) (hom y y)
      (@D₂ y y y y) (hom y x)
      (λ w, (a ∘ ((lidv ∘ lidu) ∘ (a⁻¹))))
      (λ w, a ∘ w) (λ w, id) (λ w, id) _ _ (assoc id id (a⁻¹))),
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply transport4_set_reduce, repeat ( apply homH ),
  end

  end
end gamma
