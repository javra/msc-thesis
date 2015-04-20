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

definition gamma_lambda_iso_nat (X Y : Xmod) (f : xmod_morphism X Y) :
  ((@functor.id Cat_xmod) f) ∘ (gamma_lambda_iso X)
  = (gamma_lambda_iso Y) ∘
    (@to_fun_hom _ _ (functor.compose gamma.functor lambda.functor) X Y f) :=
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
    cases X, cases Y, cases f, cases x, cases filler,
    apply inverse,
    apply concat, apply lambda.functor_on_hom_aux2,
    apply concat, apply lambda.functor_on_hom_aux3,
    apply concat, apply lambda.functor_on_hom_aux4,
    apply idp,
  },
end

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
      intros [X, Y, f], apply (gamma_lambda_iso_nat X Y f),
end
