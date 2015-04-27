import algebra.precategory.adjoint
import .gamma_functor .lambda_functor

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open gamma lambda

universe variables l--₁ l₂ l₃

definition gamma_lambda_transf_hom_family [reducible] (X : Xmod)
  (p : carrier (to_fun_ob (functor.compose gamma.functor lambda.functor) X))
  (a : groups (to_fun_ob (functor.compose gamma.functor lambda.functor) X) p) :
  groups X (to_fun_ob (@functor.id (Precategory.mk _ (Xmod.gpd X))) p) :=
by cases a; cases filler; exact m

definition gamma_lambda_transf [reducible] (X : Xmod) :
  hom (functor.compose gamma.functor lambda.functor X) X :=
begin
  fapply xmod_morphism.mk,
    apply functor.id,
    intros, apply gamma_lambda_transf_hom_family, apply a,
    { intros, cases x with [lidx, fillerx], cases y with [lidy, fillery],
      cases fillerx with [fillerxm, fillerxcomm],
      cases fillery with [fillerym, fillerycomm],
      apply concat, apply lambda_morphism_m_transport_b,
      apply (ap (λ x, fillerxm * x)),
      apply φ_respect_id,
    },
    { intros, cases x, cases filler,
      apply inverse, apply concat, apply comm,
      apply concat, apply id_left,
      apply concat, apply assoc,
      apply concat, apply (ap (λ x, _ ∘ x)), apply id_inverse,
      apply concat, apply id_right, apply id_right,
    },
    { intros, cases x, cases filler,
      apply concat, apply (refl (lambda_morphism.m _)),
      do 3 (apply concat; apply lambda_morphism_m_transport_b),
      apply concat, apply one_mul,
      apply (ap (λ x, φ X a x)),
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply (ap (λ x, m * _)), apply φ_respect_id,
      apply mul_one,
    },
end

definition gamma_lambda_transf_nat (X Y : Xmod) (f : xmod_morphism X Y) :
  ((@functor.id Cat_xmod) f) ∘ (gamma_lambda_transf X)
  = (gamma_lambda_transf Y) ∘
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
    apply lambda.functor_on_hom_aux4,
  },
end

set_option apply.class_instance false
definition gamma_lambda_transf_inv [reducible] (X : Xmod) :
  hom X (functor.compose gamma.functor lambda.functor X) :=
begin
  fapply xmod_morphism.mk,
  { apply functor.id, },
  { intros,
    fapply (@folded_sq.mk (carrier (Dbl_gpd.gpd (lambda.on_objects X)))),
      apply (μ X a),
    fapply lambda_morphism.mk, apply a,
    apply inverse, apply concat, apply id_left,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply id_inverse,
    apply concat, apply (ap (λ x, _ ∘ x)), apply id_right,
    apply id_right,
  },
  { intros,
    fapply (@folded_sq.congr (carrier (Dbl_gpd.gpd (lambda.on_objects X)))),
      apply μ_respect_comp,
    fapply lambda_morphism.congr',
      apply concat, apply lambda_morphism_m_transport_u,
      apply concat, apply (refl (x * y)),
      apply inverse, apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply (refl (x * _)),
      apply (ap (λ x, _ * x)), apply φ_respect_id,
    apply is_hset.elim,
  },
  { intros, apply idp, },
  { intros,
    fapply (@folded_sq.congr (carrier (Dbl_gpd.gpd (lambda.on_objects X)))),
      apply (CM1 X),
    fapply lambda_morphism.congr',
      apply concat, apply lambda_morphism_m_transport_u,
      apply concat, apply (refl (φ X a x)),
      apply inverse, apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply lambda_morphism_m_transport_b,
      apply concat, apply (refl (_ * _)),
      apply concat, apply one_mul,
      apply (ap (λ x, φ X a x)),
      apply concat, apply (refl (x * _)),
      apply concat, apply (ap (λ y, _ * y)), apply φ_respect_id,
      apply mul_one,
    apply is_hset.elim,
  },
end

set_option apply.class_instance true
definition gamma_lambda_transf_iso (X : Xmod.{l l l}) :
  is_iso (gamma_lambda_transf X) :=
begin
  fapply @is_iso.mk, exact (gamma_lambda_transf_inv.{l l l} X),
  { apply inverse, apply concat, apply (refl (@xmod_morphism.mk _ _ _ _ _ _ _)),
    fapply (xmod_morphism_congr
      (to_fun_ob (functor.compose gamma.functor lambda.functor) X)
      (to_fun_ob (functor.compose gamma.functor lambda.functor) X)),
        apply idp, apply idp,
    apply concat, apply tr_idp,
    apply eq_of_homotopy, intro p, apply eq_of_homotopy, intro x,
    cases x, cases filler,
    apply inverse,
    fapply (@folded_sq.congr _ _ _ _ (struct (to_fun_ob lambda.functor X))),
      apply inverse,
      apply concat, apply inverse, apply id_left,
      apply concat, apply inverse, apply (ap (λ x, _ ∘ x)), apply id_right,
      apply concat, apply inverse, apply (ap (λ x, id ∘ lid ∘ x)), apply id_right,
      apply concat, apply inverse, apply (ap (λ x, id ∘ lid ∘ x ∘ x)), apply id_inverse,
      apply concat, apply inverse, apply comm,
      apply (ap (λ x, μ X x)), apply idp,
    fapply lambda_morphism.congr',
      apply concat, apply lambda.functor_on_hom_aux1, apply idp,
    apply is_hset.elim,
  },
  { fapply xmod_morphism_congr, apply idp, apply idp,
    apply concat, apply tr_idp,
    apply eq_of_homotopy, intro p, apply eq_of_homotopy, intro x,
    apply idp,
  },
end

set_option apply.class_instance false
definition xmod_dbl_gpd_equivalence :
  equivalence Cat_dbl_gpd.{l l l} Cat_xmod.{l l l} :=
begin
  fapply equivalence.mk,
    apply gamma.functor,
  fapply is_equivalence.mk,
      apply lambda.functor,
    rotate 1,
    fapply iso.mk,
      fapply nat_trans.mk,
        intro X, apply (gamma_lambda_transf X),
      intros [X, Y, f], apply (gamma_lambda_transf_nat X Y f),
    fapply @is_iso_nat_trans,
    intro X, esimp, apply (gamma_lambda_transf_iso X),
end
