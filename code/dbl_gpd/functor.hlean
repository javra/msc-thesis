import algebra.category.functor
import ..dbl_cat.transports .decl ..transport4 ..dbl_gpd.basic arity ..transport4

open eq iso iso category
open functor dbl_gpd dbl_precat equiv Dbl_gpd
open prod prod.ops sigma sigma.ops pi is_trunc thin_structure

namespace dbl_gpd

  section
  variables (D E : Dbl_gpd)
  include D E
  variables (catF : functor (gpd D) (gpd E))
    (twoF : Π ⦃a b c d : gpd D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))

  definition respect_id₁_type [reducible] : Type := Π ⦃a b : gpd D⦄ (f : hom a b),
    transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
      (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
        (twoF (dbl_precat.ID₁ D f)))
    = dbl_precat.ID₁ E (catF f)

  definition respect_id₂_type [reducible] : Type := Π ⦃a b : gpd D⦄ (f : hom a b),
    transport (λ x, two_cell E _ x _ _) (respect_id catF b)
      (transport (λ x, two_cell E x _ _ _) (respect_id catF a)
        (twoF (dbl_precat.ID₂ D f)))
    = dbl_precat.ID₂ E (catF f)

  set_option unifier.max_steps 60000 --TODO make this go away
  definition respect_comp₁_type [reducible] : Type := Π ⦃a b c₁ d₁ c₂ d₂ : gpd D⦄
    ⦃f : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : two_cell D g₁ g₂ h₂ i₂)
    (u : two_cell D f g₁ h₁ i₁),
      transport (λ x, two_cell E (to_fun_hom catF f) (to_fun_hom catF g₂)
        (to_fun_hom catF h₂ ∘ to_fun_hom catF h₁) x)
        (respect_comp catF i₂ i₁)
        (transport (λ x, two_cell E (to_fun_hom catF f) (to_fun_hom catF g₂)
          x (to_fun_hom catF (i₂ ∘ i₁)))
          (respect_comp catF h₂ h₁)
          (twoF (dbl_precat.comp₁ D v u)))
      = dbl_precat.comp₁ E (twoF v) (twoF u)

  definition respect_comp₂_type [reducible] : Type := Π ⦃a b₁ c d₁ b₂ d₂ : gpd D⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : two_cell D f₂ g₂ i₁ i₂)
    (u : two_cell D f₁ g₁ h i₁),
      transport
        (λ x, two_cell E (to_fun_hom catF f₂ ∘ to_fun_hom catF f₁) x
        (to_fun_hom catF h) (to_fun_hom catF i₂))
        (respect_comp catF g₂ g₁)
        (transport (λ x, two_cell E x (to_fun_hom catF (g₂ ∘ g₁))
          (to_fun_hom catF h) (to_fun_hom catF i₂))
          (respect_comp catF f₂ f₁)
          (twoF (dbl_precat.comp₂ D v u)))
      = dbl_precat.comp₂ E (twoF v) (twoF u)
  set_option unifier.max_steps 20000
  end

  structure dbl_functor (D E : Dbl_gpd) :=
    (catF : functor (gpd D) (gpd E))
    (twoF : Π ⦃a b c d : gpd D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))
    (respect_id₁ : respect_id₁_type D E catF twoF)
    (respect_comp₁ : respect_comp₁_type D E catF twoF)
    (respect_id₂ : respect_id₂_type D E catF twoF)
    (respect_comp₂ : respect_comp₂_type D E catF twoF)

  definition dbl_functor_sigma_char (D E : Dbl_gpd) :
    (Σ (catF : functor (gpd D) (gpd E))
       (twoF : Π ⦃a b c d : gpd D⦄
         ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
         two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i)),
       prod (respect_id₁_type D E catF twoF)
        (prod (respect_comp₁_type D E catF twoF)
         (prod (respect_id₂_type D E catF twoF)
          (respect_comp₂_type D E catF twoF)))) ≃ (dbl_functor D E) :=
  begin
    fapply equiv.mk,
      begin
        intro S, fapply dbl_functor.mk,
        apply (S.1), exact (@S.2.1), exact (pr1 @S.2.2),
        exact (pr1 (pr2 @S.2.2)), exact (pr1 (pr2 (pr2 @S.2.2))),
        exact (pr2 (pr2 (pr2 @S.2.2)))
      end,
      begin
        fapply is_equiv.adjointify,
          {intro F, cases F,
           apply (sigma.mk catF (sigma.mk twoF
                   (respect_id₁ , (respect_comp₁, (respect_id₂, respect_comp₂)))))},
          {intro F, cases F, apply idp},
          {intro S,
           cases S    with [catF, S'],
           cases S'   with [twoF, S''],
           cases S''  with [respect_id₁, S'''],
           cases S''' with [respect_comp₁, S''''],
           cases S'''',
           apply idp}
      end
  end

  section
  parameters (D E : Dbl_gpd)
    (catF1 catF2 : functor (gpd D) (gpd E))
    (twoF1 : Π ⦃a b c d : gpd D⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF1 f) (catF1 g) (catF1 h) (catF1 i))
    (twoF2 : Π ⦃a b c d : gpd D⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF2 f) (catF2 g) (catF2 h) (catF2 i))

  definition respect_id₁1_type [reducible] := respect_id₁_type D E catF1
  definition respect_id₁2_type [reducible] := respect_id₁_type D E catF2
  definition respect_comp₁1_type [reducible] := respect_comp₁_type D E catF1
  definition respect_comp₁2_type [reducible] := respect_comp₁_type D E catF2
  definition respect_id₂1_type [reducible] := respect_id₂_type D E catF1
  definition respect_id₂2_type [reducible] := respect_id₂_type D E catF2
  definition respect_comp₂1_type [reducible] := respect_comp₂_type D E catF1
  definition respect_comp₂2_type [reducible] := respect_comp₂_type D E catF2

  parameters
    (respect_id₁1 : respect_id₁1_type twoF1)
    (respect_id₁2 : respect_id₁2_type twoF2)
    (respect_comp₁1 : respect_comp₁1_type twoF1)
    (respect_comp₁2 : respect_comp₁2_type twoF2)
    (respect_id₂1 : respect_id₂1_type twoF1)
    (respect_id₂2 : respect_id₂2_type twoF2)
    (respect_comp₂1 : respect_comp₂1_type twoF1)
    (respect_comp₂2 : respect_comp₂2_type twoF2)

  definition dbl_functor.congr (p1 : catF1 = catF2) (p2 : p1 ▸ twoF1 = twoF2) :
    dbl_functor.mk catF1 twoF1
      respect_id₁1 respect_comp₁1 respect_id₂1 respect_comp₂1
    = dbl_functor.mk catF2 twoF2
      respect_id₁2 respect_comp₁2 respect_id₂2 respect_comp₂2 :=
  begin
    cases p1, cases p2,
    intros, apply (ap01111 (λ f g h i, dbl_functor.mk catF2 twoF2 f g h i)),
      repeat (
        repeat ( apply eq_of_homotopy ; intros ) ;
        apply (@is_hset.elim _ (!(homH' E))) ),
  end

  parameters
    (p1 : to_fun_ob catF1 = to_fun_ob catF2)
    (p2 : transport
      (λ x, Π (a b : carrier (gpd D)), hom a b → hom (x a) (x b)) p1
      @(to_fun_hom catF1) = @(to_fun_hom catF2))
    (p3 : apd011 (λ Hob Hhom,
                  Π ⦃a b c d : carrier (gpd D)⦄
                    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
                    two_cell D f g h i →
                    @two_cell E (Hob a) (Hob b) (Hob c) (Hob d)
                     (Hhom a b f) (Hhom c d g) (Hhom a c h) (Hhom b d i))
          p1 p2 ▸ twoF1 = twoF2)

  include p1 p2 p3
  definition dbl_functor.congr' :
    dbl_functor.mk catF1 twoF1 respect_id₁1 respect_comp₁1 respect_id₂1 respect_comp₂1
    = dbl_functor.mk catF2 twoF2 respect_id₁2 respect_comp₁2 respect_id₂2 respect_comp₂2 :=
  begin
    cases catF1 with [catF11, catF12, catF13, catF14],
    cases catF2 with [catF21, catF22, catF23, catF24],
    cases p1, cases p2, cases p3,
    assert P2 : catF13 = catF23,
      apply is_hprop.elim,
    cases P2,
    assert P3 : @catF14 = @catF24,
      apply is_hprop.elim,
    cases P3,
    assert P4 : respect_id₁1 = respect_id₁2,
      repeat ( apply eq_of_homotopy ; intros ),
      apply (@is_hset.elim _ (!(homH' E))),
    cases P4,
    assert P5 : respect_comp₁1 = respect_comp₁2,
      repeat ( apply eq_of_homotopy ; intros ),
      apply (@is_hset.elim _ (!(homH' E))),
    cases P5,
    assert P6 : respect_id₂1 = respect_id₂2,
      repeat ( apply eq_of_homotopy ; intros ),
      apply (@is_hset.elim _ (!(homH' E))),
    cases P6,
    assert P7 : respect_comp₂1 = respect_comp₂2,
      repeat ( apply eq_of_homotopy ; intros ),
      apply (@is_hset.elim _ (!(homH' E))),
    cases P7,
    apply idp,
  end

  end

  open dbl_functor

  definition respect_id₁' {D E : Dbl_gpd} (F : dbl_functor D E)
    {a b : gpd D} (f : hom a b) :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq (respect_id₁ F f))

  definition respect_id₂' {D E : Dbl_gpd} (F : dbl_functor D E)
    {a b : gpd D} (f : hom a b) :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq (respect_id₂ F f))

  section
  parameters {D E : Dbl_gpd} (F : dbl_functor D E)
    ⦃a b c₁ d₁ c₂ d₂ : gpd D⦄
    ⦃f : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : two_cell D g₁ g₂ h₂ i₂)
    (u : two_cell D f g₁ h₁ i₁)

  definition respect_comp₁' :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq (respect_comp₁ F v u))

  end

  section
  parameters {D E : Dbl_gpd} (F : dbl_functor D E)
    ⦃a b₁ c d₁ b₂ d₂ : gpd D⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : two_cell D f₂ g₂ i₁ i₂)
    (u : two_cell D f₁ g₁ h i₁)

  definition respect_comp₂' :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq (respect_comp₂ F v u))

  end

  section
  parameters
    {D E : Dbl_gpd} (F : dbl_functor D E)
    {a b c d : gpd D} {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}

  definition twoF_transport_u {I : Type} (e : I → hom a b)
    {f f' : I} (pf : f = f') (u : two_cell D (e f) g h i) :
    twoF F (pf ▸ u) = pf ▸ (twoF F u) :=
  by cases pf; apply idp

  definition twoF_transport_b  {I : Type} (e : I → hom c d)
    {g g' : I} (pg : g = g') (u : two_cell D f (e g) h i) :
    twoF F (pg ▸ u) = pg ▸ (twoF F u) :=
  by cases pg; apply idp

  definition twoF_transport_l  {I : Type} (e : I → hom a c)
    {h h' : I} (ph : h = h') (u : two_cell D f g (e h) i) :
    twoF F (ph ▸ u) = ph ▸ (twoF F u) :=
  by cases ph; apply idp

  definition twoF_transport_r  {I : Type} (e : I → hom b d)
    {i i' : I} (pi : i = i') (u : two_cell D f g h (e i)) :
    twoF F (pi ▸ u) = pi ▸ (twoF F u) :=
  by cases pi; apply idp

  end

  section
  parameters {D E : Dbl_gpd} (F : dbl_functor D E)
    {a b c d : gpd D} {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : two_cell D f g h i)

  definition respect_inv₁ :
    transport (λ x, two_cell E _ _ _ x) (functor.respect_inv (catF F) i)
      (transport (λ x, two_cell E _ _ x _) (functor.respect_inv (catF F) h)
        (twoF F (inv₁ D u)))
    = inv₁ E (twoF F u) :=
  begin
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (id_right₁ E (twoF F (inv₁ D u))),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₁ E _ x)),
      apply inverse, apply (right_inverse₁ E (twoF F u)),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_u_r E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_u_l E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (assoc₁' E),
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ E x _)),
      apply inverse, apply  (respect_comp₁ F),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_r E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_l E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₁ E (twoF F x) _)), apply (left_inverse₁' D),
    apply concat, apply (ap (λ x, comp₁ E x _)), apply twoF_transport_l,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_l E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ E x _)), apply twoF_transport_r,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_r E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ E x _)), apply (respect_id₁' F),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_l E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_r E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (id_left₁' E),
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
    do 15 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

  definition respect_inv₁' :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq respect_inv₁)

  definition respect_inv₂ :
    transport (λ x, two_cell E _ x _ _) (functor.respect_inv (catF F) g)
      (transport (λ x, two_cell E x _ _ _) (functor.respect_inv (catF F) f)
        (twoF F (inv₂ D u)))
    = inv₂ E (twoF F u) :=
  begin
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (id_right₂ E (twoF F (inv₂ D u))),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ E _ x)),
      apply inverse, apply (right_inverse₂ E (twoF F u)),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (assoc₂' E),
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ E x _)),
      apply inverse, apply (respect_comp₂ F),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' E),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ E (twoF F x) _)), apply (left_inverse₂' D),
    apply concat, apply (ap (λ x, comp₂ E x _)), apply twoF_transport_u,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ E x _)), apply twoF_transport_b,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ E x _)), apply (respect_id₂' F),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' E),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (id_left₂' E),
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
    do 15 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

  definition respect_inv₂' :=
  eq_inv_tr_of_tr_eq (eq_inv_tr_of_tr_eq respect_inv₂)

  end

  section
  parameters {D E : Dbl_gpd} (F : dbl_functor D E) {a b : gpd D} (f : hom a b)

  -- This is a helper lemma for the equivalence construction.
  -- TODO: replace it by use of the above lemmas.
  definition respect_id₁''_lhs [reducible] := twoF F (dbl_precat.ID₁ D (f⁻¹))
  definition respect_id₁''_rhs [reducible] := transport (λ x, two_cell E x _ _ _)
  (@functor.respect_inv _ _ (catF F) _ _ f (!all_iso) (!all_iso))⁻¹
  (transport (λ x, two_cell E _ x _ _)
  (@functor.respect_inv _ _ (catF F) _ _ f (!all_iso) (!all_iso))⁻¹
  (transport (λ x, two_cell E _ _ x _) (eq.inverse (respect_id (catF F) b))
  (transport (λ x, two_cell E _ _ _ x) (eq.inverse (respect_id (catF F) a))
  proof (dbl_precat.ID₁ E (to_fun_hom (catF F) f)⁻¹) qed)))

  definition respect_id₁''_aux := 
  eq_inv_tr_of_tr_eq (apd (λ x, dbl_precat.ID₁ E x) (functor.respect_inv (catF F) f))

  definition respect_id₁'' : respect_id₁''_lhs = respect_id₁''_rhs :=
  begin
    apply concat, apply (respect_id₁' F),
    do 2 (apply inv_tr_eq_of_eq_tr),
    apply concat, apply respect_id₁''_aux,
    apply inv_tr_eq_of_eq_tr, apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
    do 6 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

  end

  definition dbl_functor.compose [reducible] {C D E : Dbl_gpd}
    (G : dbl_functor D E) (F : dbl_functor C D) : dbl_functor C E :=
  begin
    fapply dbl_functor.mk,
      apply (functor.compose (catF G) (catF F)),
      intros, apply (twoF G (twoF F a_1)),
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_id₁',
        apply concat, apply twoF_transport_l, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_r, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_id₁',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        apply inverse,
        apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
        do 5 (apply concat; apply transport4_transport_acc),
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_comp₁',
        apply concat, apply twoF_transport_l, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_r, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_comp₁',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        unfold functor.compose, esimp,
        apply inverse,
        apply concat,  apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
        do 5 (apply concat; apply transport4_transport_acc),
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_id₂',
        apply concat, apply twoF_transport_u, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_b, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_id₂',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        apply inverse,
        apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
        do 5 (apply concat; apply transport4_transport_acc),
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_comp₂',
        apply concat, apply twoF_transport_u, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_b, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_comp₂',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        unfold functor.compose, esimp,
        apply inverse,
        apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell E f g h i)),
        do 5 (apply concat; apply transport4_transport_acc),
        apply transport4_set_reduce,
  end

  definition dbl_functor.id (C : Dbl_gpd) : dbl_functor C C :=
  begin
    fapply dbl_functor.mk,
      apply functor.id,
      intros, apply a_1,
      intros, apply idp,
      intros, apply idp,
      intros, apply idp,
      intros, apply idp,
  end

  --Algebraicly motivated congruence lemma for double functors
  section
  parameters
    {D E : Dbl_gpd}
    (F G : dbl_functor D E)
    (p : Π (a : gpd D), catF F a = catF G a)

  definition p_iso [reducible] := λ x, to_hom (iso_of_eq (p x))
  attribute iso.struct [instance]

  parameter (q : Π ⦃a b : gpd D⦄ (f : hom a b), catF G f ∘ p_iso a = p_iso b ∘ catF F f)

  section
  parameters ⦃a b c d : gpd D⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d)
    (u : two_cell D f g h i)

  definition alg_congr_br [reducible] :=
  thin E (p_iso d) (ID (catF G d)) (p_iso d) (ID (catF G d)) idp

  definition alg_congr_b [reducible] :=
  thin E (catF F g) (catF G g) (p_iso c) (p_iso d) (q g)

  definition alg_congr_bl [reducible] :=
  thin E (p_iso c)⁻¹ (ID (catF G c)) (ID (catF G c)) (p_iso c)
  begin
    apply concat, apply id_left, apply inverse, apply comp.right_inverse,
  end

  definition alg_congr_r [reducible] :=
  thin E (p_iso b) (p_iso d) (catF F i) (catF G i) (q i)⁻¹

  include q
  definition alg_congr_l [reducible] :=
  thin E (p_iso a)⁻¹ (p_iso c)⁻¹ (catF G h) (catF F h)
  begin
    apply inverse_comp_eq_of_eq_comp, apply inverse, apply concat, apply assoc,
    apply comp_inverse_eq_of_eq_comp, apply inverse, apply q,
  end

  definition alg_congr_ur [reducible] :=
  thin E (ID (catF G b)) (p_iso b) (p_iso b)⁻¹ (ID (catF G b))
  begin
    apply concat, apply comp.right_inverse,
    apply inverse, apply id_left,
  end

  definition alg_congr_u [reducible] :=
  thin E (catF G f) (catF F f) (p_iso a)⁻¹ (p_iso b)⁻¹
  begin
    apply eq_inverse_comp_of_comp_eq, apply concat, apply assoc,
    apply comp_inverse_eq_of_eq_comp, apply inverse, apply q,
  end

  definition alg_congr_ul [reducible] :=
  thin E (ID (catF G a)) (p_iso a)⁻¹ (ID (catF G a)) (p_iso a)⁻¹
  begin
    apply idp,
  end

  definition alg_congr_lhs [reducible] :=
  comp₁ E
    (comp₂ E alg_congr_br (comp₂ E alg_congr_b alg_congr_bl))
    (comp₁ E
      (comp₂ E alg_congr_r (comp₂ E (twoF F u) alg_congr_l))
      (comp₂ E alg_congr_ur (comp₂ E alg_congr_u alg_congr_ul)))

  definition alg_congr_lhs' [reducible] :=
  (transport (λ x, two_cell E x _ _ _) (id_left (catF G f))
   (transport (λ x, two_cell E _ x _ _) (id_left (catF G g))
    (transport (λ x, two_cell E _ _ x _) (id_left (catF G h))
     (transport (λ x, two_cell E _ _ _ x) (id_left (catF G i))
      (transport (λ x, two_cell E (_ ∘ x) _ _ _) (id_right (catF G f))
       (transport (λ x, two_cell E _ (_ ∘ x) _ _) (id_right (catF G g))
        (transport (λ x, two_cell E _ _ (_ ∘ x) _) (id_right (catF G h))
         (transport (λ x, two_cell E _ _ _ (_ ∘ x)) (id_right (catF G i))
            alg_congr_lhs))))))))

  definition alg_congr_s [reducible] := alg_congr_lhs' = twoF G u

  end

  parameter (all_s : Π ⦃a b c d : gpd D⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : two_cell D f g h i), alg_congr_s f g h i u)

  include p q all_s
  --set_option pp.notation false
  --TODO: complete this!!
  /-protected definition alg_congr : F = G :=
  begin
    cases F with (F1, F2, F3, F4, F5, F6),
    cases G with (G1, G2, G3, G4, G5, G6),
    fapply congr,
      fapply functor_eq_mk,
        intro a, exact (p a),
        intros (a, b, f),
  end-/

  end

  definition dbl_functor.assoc {B C D E : Dbl_gpd}
    (H : dbl_functor D E) (G : dbl_functor C D) (F : dbl_functor B C) :
    dbl_functor.compose H (dbl_functor.compose G F)
    = dbl_functor.compose (dbl_functor.compose H G) F :=
  begin
    fapply (dbl_functor.congr' B E),
        apply idp,
      apply idp,
    apply idp,
  end

  definition dbl_functor.id_left {B C : Dbl_gpd} (F : dbl_functor B C) :
    dbl_functor.compose (dbl_functor.id C) F = F :=
  begin
    cases F with [F1, F2, F3, F4, F5, F6],
    fapply (dbl_functor.congr' B C),
        apply idp,
      apply idp,
    apply idp,
  end

  definition dbl_functor.id_right {B C : Dbl_gpd} (F : dbl_functor B C) :
    dbl_functor.compose F (dbl_functor.id B) = F :=
  begin
    cases F with [F1, F2, F3, F4, F5, F6],
    fapply (dbl_functor.congr' B C),
        apply idp,
      apply idp,
    apply idp,
  end

end dbl_gpd
