import .gamma ..dbl_gpd.functor ..xmod.morphism

open eq function category iso dbl_gpd xmod is_trunc path_algebra functor dbl_precat

namespace gamma

  --set_option pp.notation false
  set_option pp.max_steps 10000
  protected definition on_morphisms (G H : Dbl_gpd) (F : dbl_functor G H) :
    xmod_morphism (gamma.on_objects G) (gamma.on_objects H) :=
  begin
    cases F with (catF, twoF, F3, F4, F5, F6),
    cases G with (gpdG,sqG,structG,carrierG_hset),
    cases H with (gpdH,sqH,structH,carrierH_hset),
    fapply xmod_morphism.mk,
    apply catF,
    { intros (p, x), cases x with (lid,filler),
      fapply M_morphism.mk, apply (to_fun_hom catF lid),
      apply (transport (λ x, sqH _ x id id) (respect_id catF p)),
      apply (transport (λ x, sqH _ _ x id) (respect_id catF p)),
      apply (transport (λ x, sqH _ _ _ x) (respect_id catF p)),
      apply (twoF filler),
    },
    { intros,
      cases x with (lidx,fillerx),
      cases y with (lidy,fillery),
      fapply M_morphism.congr, apply (respect_comp catF),
      esimp{M_morphism.cases_on,M_morphism.filler},
      apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
      apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
      apply concat, apply (twoF_transport_b (dbl_functor.mk catF twoF F3 F4 F5 F6)),
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply respect_comp₂',
      apply inverse, apply tr_eq_of_eq_inv_tr,
      apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
      apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr, apply tr_eq_of_eq_inv_tr,
      esimp{dbl_functor.catF,dbl_functor.twoF,M_morphism.lid},
      apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b,
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b,
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_l,
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_inner,
      apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_r,
      apply tr_eq_of_eq_inv_tr, apply inverse,
      apply concat, apply (transport_eq_transport4 (λ f g h i, sqH f g h i)
        (λ x, catF lidx ∘ catF lidy) (λ x, (catF (ID p)) ∘ (catF (ID p)))
        (λ x, catF (ID p)) (λ x, x) (respect_id catF p)⁻¹),
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
    },
  end

end gamma
