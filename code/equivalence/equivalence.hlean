import algebra.precategory.adjoint
import .gamma_functor .lambda_functor

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open gamma lambda

universe variables l₁ l₂ l₃

--set_option pp.notation false
--set_option pp.implicit true
definition gamma_lambda_iso_hom_family [reducible] (X : Xmod)
  (p : carrier (to_fun_ob (functor.compose gamma.functor lambda.functor) X))
  (a : groups (to_fun_ob (functor.compose gamma.functor lambda.functor) X) p) :
  groups X (to_fun_ob (@functor.id (Precategory.mk _ (Xmod.gpd X))) p) :=
by cases a; cases filler; exact m

definition gamma_lambda_iso (X : Xmod) :
  hom (functor.compose gamma.functor lambda.functor X) X :=
begin
  fapply xmod_morphism.mk,
    apply functor.id,
    intros, apply gamma_lambda_iso_hom_family, apply a,
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
      apply (ap (λ x, φ X a x)),
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply (ap (λ x, m * _)), apply φ_respect_id,
      apply mul_one,
    },
end

set_option pp.max_steps 10000
check xmod_morphism.mk

definition gamma_lambda_iso_nat (X Y : Xmod) (f : xmod_morphism X Y) :
    (@comp (carrier Cat_xmod) Cat_xmod
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) X)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) Y)
       (@to_fun_hom Cat_xmod Cat_xmod (@functor.id Cat_xmod) X Y f)
       (gamma_lambda_iso X))
    = (@comp (carrier Cat_xmod) Cat_xmod
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor) X)
       (@to_fun_ob Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor) Y)
       (@to_fun_ob Cat_xmod Cat_xmod (@functor.id Cat_xmod) Y)
       (gamma_lambda_iso Y)
       (@to_fun_hom Cat_xmod Cat_xmod
          (@functor.compose Cat_xmod Cat_dbl_gpd Cat_xmod gamma.functor lambda.functor)
          X Y f)) :=
begin
  fapply xmod_morphism_congr,
  { cases X, cases Y, cases f,
    apply idp,
  },
  { cases X, cases Y, cases f,
    apply idp,
  },
  { apply eq_of_homotopy, intro p,
    apply eq_of_homotopy, intro x,
    cases X with [X1, X2, X3, X'],-- cases X' with [X4, X5, X6, X7, X8, X9, X10, X11, X12],
    cases Y with [Y1, Y2, Y3, Y'],-- cases Y' with [Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12],
    cases f with [f1, f2, f3, f4, f5],
    cases x, cases filler,
    esimp [Xmod.cases_on, xmod_morphism.cases_on],
    apply concat, apply (refl (f2 p m)),
    apply inverse, apply concat, apply (refl (gamma_lambda_iso_hom_family _ _ _)),
    esimp [gamma_lambda_iso_hom_family, folded_sq.mk, folded_sq.cases_on],
    esimp [lambda_morphism.cases_on, lambda_morphism.m],
    apply concat, apply lambda.functor_on_hom_aux2,
    apply concat, apply lambda.functor_on_hom_aux3,
    apply concat, apply lambda.functor_on_hom_aux4,
    apply idp,
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

definition xmod_dbl_gpd_equivalence :
  equivalence Cat_dbl_gpd.{(max l₁ l₂) l₂ l₃} Cat_xmod.{(max l₁ l₂) l₂ l₃} :=
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
