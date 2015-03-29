import .lambda_morphisms

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd functor

namespace lambda

  universe variables l1 l2 l3

  protected definition functor :
    functor Cat_xmod.{l1 l2 l3} Cat_dbl_gpd.{(max l1 l2) l2 l3} :=
  begin
    fapply functor.mk,
      intro X, apply (lambda.on_objects X),
      intros [X, Y, f], apply (lambda.on_morphisms f),
      intro X, cases X,
        fapply dbl_functor.congr',
            apply idp,
          apply idp,
        repeat ( apply eq_of_homotopy ; intros), cases x_8,
        fapply lambda_morphism.congr', apply idp,
        apply is_hset.elim,
      intros [X, Y, Z, g, f], cases X, cases Y, cases Z, cases g, cases f,
        fapply dbl_functor.congr',
            apply idp,
          apply idp,
        repeat ( apply eq_of_homotopy ; intros), cases x_8,
        fapply lambda_morphism.congr', apply idp,
        apply is_hset.elim,
  end

end lambda
