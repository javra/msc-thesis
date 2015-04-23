import .gamma ..dbl_gpd.functor ..xmod.morphism

open eq category iso is_trunc path_algebra function xmod dbl_precat dbl_gpd Dbl_gpd functor

namespace gamma
  section
  parameters {G H : Dbl_gpd} (F : dbl_functor G H)

  protected definition on_morphisms_on_base [reducible] (p : gamma.on_objects G)
    (x : Xmod.groups (gamma.on_objects G) p) :
    Xmod.groups (gamma.on_objects H) (to_fun_ob (dbl_functor.catF F) p) :=
  begin
    cases F with [catF, twoF, F3, F4, F5, F6],
    cases G with [gpdG,sqG,structG,carrierG_hset],
    cases H with [gpdH,sqH,structH,carrierH_hset],
    cases x with [lid,filler],
    fapply folded_sq.mk, apply (to_fun_hom catF lid),
    apply (transport (λ x, sqH _ x id id) (respect_id catF p)),
    apply (transport (λ x, sqH _ _ x id) (respect_id catF p)),
    apply (transport (λ x, sqH _ _ _ x) (respect_id catF p)),
    apply (twoF filler),
  end

  set_option unifier.max_steps 30000
  protected definition on_morphisms_hom_family [reducible]
    (p : Xmod.carrier (gamma.on_objects G)) (x y : Xmod.groups (gamma.on_objects G) p) :
    gamma.on_morphisms_on_base F p (x * y)
    = (gamma.on_morphisms_on_base F p x) * (gamma.on_morphisms_on_base F p y) :=
  begin
    cases F with [catF, twoF, F3, F4, F5, F6],
    cases G with [gpdG,sqG,structG,carrierG_hset],
    cases H with [gpdH,sqH,structH,carrierH_hset],
    cases x with [lidx,fillerx],
    cases y with [lidy,fillery],
    fapply folded_sq.congr, apply (respect_comp catF),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_b (dbl_functor.mk catF twoF F3 F4 F5 F6)),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply respect_comp₂',
    apply inverse, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_l,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_inner,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_r,
    apply tr_eq_of_eq_inv_tr, apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, sqH f g h i)),
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

  include F
  set_option apply.class_instance false
  --set_option pp.full_names true
  set_option pp.max_depth 10000
  set_option pp.max_steps 50000

  protected definition on_morphisms :
    xmod_morphism (gamma.on_objects G) (gamma.on_objects H) :=
  begin
    fapply xmod_morphism.mk,
    apply (dbl_functor.catF F),
    intros [p, x], apply (on_morphisms_on_base p x),
    intros [p, x, y], apply (on_morphisms_hom_family p x y),
    intros, cases x, cases F, cases G, cases H, apply idp,
    intros, cases x with [lidx,fillerx],
    cases F with [catF, twoF, F3, F4, F5, F6],
    cases G with [gpdG, sqG, structG, carrierG_hset],
    cases H with [gpdH, sqH, structH, carrierH_hset],
    fapply folded_sq.congr,
      apply concat, apply respect_comp,
      apply concat, apply (ap (λ x, _ ∘ x)), apply respect_comp,
      apply (ap (λ x, _ ∘ _ ∘ x)),
        apply (@functor.respect_inv _ _ catF _ _ a (!all_iso) (!all_iso)),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_b (dbl_functor.mk catF twoF F3 F4 F5 F6) (λ x, x)
        (@right_inverse _ _ _ _ a (!all_iso))),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_b (dbl_functor.mk catF twoF F3 F4 F5 F6) _
                        (id_left (@iso.inverse _ _ _ _ a (!all_iso)))),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply respect_comp₂',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ structH
      (dbl_functor.twoF (dbl_functor.mk catF twoF F3 F4 F5 F6) (dbl_precat.ID₁ structG a)) x)),
    apply respect_comp₂',
    apply concat, apply inverse,
    apply transp_comp₂_eq_comp₂_transp_l_u', apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse,
    apply transp_comp₂_eq_comp₂_transp_l_b', apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ _ x _)), apply respect_id₁',
    apply concat, apply (ap (λ x, comp₂ _ _ x)),
    apply (ap (λ x, comp₂ (mk gpdH sqH structH carrierH_hset) (twoF fillerx) x)),
      apply respect_id₁'',
    apply concat, apply inverse, apply (ap (λ x, comp₂ _ _ x)),
    apply (transp_comp₂_eq_comp₂_transp_l_u' structH),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' structH),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (ap (λ x, comp₂ _ _ x)),
    apply (transp_comp₂_eq_comp₂_transp_l_b' structH),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' structH),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (ap (λ x, comp₂ _ _ x)),
    apply transp_comp₂_eq_comp₂_transp_l_l,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_l structH),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (transp_comp₂_inner_deal1 structH),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_r structH),
    apply inv_tr_eq_of_eq_tr,
    apply inverse,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ structH
      (dbl_precat.ID₁ structH (to_fun_hom catF a)) x)),
    apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' structH),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' structH),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ _ _ x)), apply (transp_comp₂_inner_deal2 structH),
    apply concat, apply (ap (λ x, comp₂ _ _ x)), apply inverse,
    apply (transp_comp₂_eq_comp₂_transp_r_r structH),
    apply inverse, apply concat,
    apply (transport_eq_transport4 (λ f g h i, sqH f g h i)),
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
    apply transport4_set_reduce,
      apply homH, apply homH, apply homH, apply homH,
  end

  end
end gamma
