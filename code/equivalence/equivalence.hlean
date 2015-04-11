import algebra.precategory.adjoint
import .gamma_functor .lambda_functor

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open gamma lambda

universe variable l

--set_option pp.notation false
--set_option pp.implicit true
definition gamma_lambda_iso (X : Xmod) :
  hom (functor.compose gamma.functor lambda.functor X) X :=
begin
  fapply xmod_morphism.mk,
    apply functor.id,
    intros, cases a, cases filler, apply m,
    { intros, cases x with [lidx, fillerx], cases y with [lidy, fillery],
      cases fillerx with [fillerxm, fillerxcomm],
      cases fillery with [fillerym, fillerycomm],
      apply concat, apply lambda_morphism_m_transport_b,
      apply (ap (λ x, fillerxm * x)),
      apply φ_respect_id,
    },
    {
      intros, cases x, cases filler,
      apply inverse, apply concat, apply comm,
      apply concat, apply id_left,
      apply concat, apply assoc,
      apply concat, apply (ap (λ x, _ ∘ x)), apply id_inverse,
      apply concat, apply id_right, apply id_right,
    },
    {
      intros, cases x, cases filler,
      apply concat, apply (refl (lambda_morphism.m _)),
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply one_mul,
      apply (ap (λ x, φ a x)),
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply (ap (λ x, m * _)), apply φ_respect_id,
      apply mul_one,
    },
end

set_option pp.max_steps 10000
print definition gamma_lambda_iso

definition gamma_lambda_iso_nat (X Y : Xmod) (m : xmod_morphism X Y) :
  @eq
    (@hom (carrier Cat_xmod) Cat_xmod
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) Y))
    (@comp (carrier Cat_xmod) Cat_xmod
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) X)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) Y)
       (@to_fun_hom Cat_xmod Cat_xmod (@functor.id Cat_xmod) X Y m)
       (gamma_lambda_iso X))
    (@comp (carrier Cat_xmod) Cat_xmod
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X)
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          Y)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) Y)
       (gamma_lambda_iso Y)
       (@to_fun_hom Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X
          Y
          m)) :=
begin
  fapply xmod_morphism_congr,
  { cases X, cases Y, cases m,
    apply idp,
  },
  { cases X, cases Y, cases m,
    apply idp,
  },
  { apply eq_of_homotopy, intro p,
    apply eq_of_homotopy, intro x,
    cases X, cases Y, cases m,
    esimp[Xmod.cases_on, xmod_morphism.cases_on],

  },
end

check @xmod_morphism.hom_family

definition lambda_gamma_iso (G : carrier Cat_dbl_gpd) :
  hom (functor.compose lambda.functor gamma.functor G) G :=
begin
  fapply dbl_functor.mk,
    apply functor.id,
    intros [a,b,c,d,f,g,h,i,u],
end

definition xmod_dbl_gpd_equivalence cd : equivalence Cat_dbl_gpd.{l l l} Cat_xmod.{l l l} :=
begin
  fapply equivalence.mk,
    apply gamma.functor,
  fapply is_equivalence.mk,
      apply lambda.functor,
    rotate 1,
    fapply iso.mk,
      fapply nat_trans.mk,
        intro X, apply (gamma_lambda_iso X),
      intros [X, Y, m],
end
