import .gamma_morphisms ..xmod.category_of ..dbl_gpd.category_of

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor

namespace gamma

  universe variable l

  set_option apply.class_instance false
  protected definition functor :
    functor Cat_dbl_gpd.{l l l} Cat_xmod.{l l l} :=
  begin
    fapply functor.mk,
      intro G, apply (gamma.on_objects G),
      intros [G, H, F], apply (gamma.on_morphisms F),
      intro G, cases G,
        fapply xmod_morphism_congr,
            apply idp,
          apply idp,
        repeat ( apply eq_of_homotopy ; intros), cases x_1, apply idp,
    intros [G, H, I, E, F],
    fapply xmod_morphism_congr,
        apply idp,
      apply idp,
    apply eq_of_homotopy, intro p,
    apply eq_of_homotopy, intro m, cases m,
    cases G, cases H, cases I,
    cases E with [E1, E2, E3, E4, E5, E6],
    cases F with [F1, F2, F3, F4, F5, F6],
    fapply M_morphism.congr',
      apply idp,
    apply inverse,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_b (dbl_functor.mk E1 E2 E3 E4 E5 E6)),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_l (dbl_functor.mk E1 E2 E3 E4 E5 E6)),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply (twoF_transport_r (dbl_functor.mk E1 E2 E3 E4 E5 E6)),
    apply tr_eq_of_eq_inv_tr,
    apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell_2 f g h i)),
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    esimp,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    esimp,
    apply @transport4_set_reduce,
    apply homH, apply homH, apply homH, apply homH,
  end


end gamma
