import algebra.precategory.adjoint
import .gamma_functor .lambda_functor

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open gamma lambda

universe variable l

--set_option pp.notation false
definition gamma_lambda_iso (X : Xmod) :
  hom (functor.compose gamma.functor lambda.functor X) X :=
begin
  fapply xmod_morphism.mk,
    apply functor.id,
    intros, cases a, cases filler, apply m,
    { intros, cases x with [lidx, fillerx], cases y with [lidy, fillery],
      cases fillerx with [fillerxm, fillerxcomm],
      cases fillery with [fillerym, fillerycomm],
      apply inverse, apply concat, apply (refl (fillerxm * fillerym)),
      apply inverse,
      apply concat, apply (ap (λ x, M_morphism.cases_on x _)),

    },
end

print definition lambda_morphism.comp₂

definition lambda_gamma_iso (G : carrier Cat_dbl_gpd) :
  hom (functor.compose lambda.functor gamma.functor G) G :=
begin
  fapply dbl_functor.mk,
    apply functor.id,
    intros [a,b,c,d,f,g,h,i,u],
end

definition xmod_dbl_gpd_equivalence : equivalence Cat_dbl_gpd.{l l l} Cat_xmod.{l l l} :=
begin
  fapply equivalence.mk,
    apply gamma.functor,
  fapply is_equivalence.mk,
      apply lambda.functor,
    rotate 1,
    fapply iso.mk,
      fapply nat_trans.mk,
        intro X,
end

check gamma.functor
