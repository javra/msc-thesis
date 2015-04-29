import algebra.precategory.adjoint
import .gamma_functor .lambda_functor ..dbl_gpd.basic

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open dbl_precat
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

section
  parameters (G : Dbl_gpd) ⦃a b c d : carrier (Dbl_gpd.gpd G)⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : two_cell G f g h i)

  definition lambda_gamma_fold [reducible] :=
  transport (λ x, two_cell G _ x _ _) (!right_inverse)
   (transport (λ x, two_cell G _ (_ ∘ x) _ _) (!id_left)
    (transport (λ x, two_cell G _ x _ _) (!id_left)
     (comp₂ G (br_connect G i) (comp₂ G u (comp₂ G (bl_connect' G h) (ID₁ G (g⁻¹)))))))

end


set_option apply.class_instance false
definition lambda_gamma_transf (G : Dbl_gpd) :
  dbl_functor G (functor.compose lambda.functor gamma.functor G) :=
begin
  fapply dbl_functor.mk, apply functor.id,
  { intros [a,b,c,d,f,g,h,i,u],
    fapply lambda_morphism.mk,
      fapply (@folded_sq.mk (carrier (Dbl_gpd.gpd G))),
        apply (i ∘ f ∘ h⁻¹ ∘ g⁻¹),
      apply (lambda_gamma_fold _ u),
    apply idp,
  },
  { intros,
    fapply lambda_morphism.congr,
      fapply folded_sq.congr,
        apply concat, apply id_left,
        apply concat, apply (ap (λ x, _ ∘ x ∘ _)), apply id_inverse,
        apply concat, apply (ap (λ x, _ ∘ x)), apply id_left,
        apply right_inverse,
      esimp[lambda_gamma_fold],
      do 4 (apply tr_eq_of_eq_inv_tr),
      apply concat, apply (ap (λ x, comp₂ G x _)), apply br_connect_id_eq_ID₁,
      apply concat, apply (ap (λ x, comp₂ G x _)), apply zero_unique,
      apply concat, apply (id_left₂' G), do 2 (apply tr_eq_of_eq_inv_tr),
      apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G x _))), apply bl_connect'_id_eq_ID₁,
      apply concat, apply (ap (λ x, comp₂ G _ x)), apply inverse,
        apply (transp_comp₂_eq_comp₂_transp_r_u' G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
      apply inv_tr_eq_of_eq_tr,
      apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G x _))), apply zero_unique,
      apply concat, apply (ap (λ x, comp₂ G _ x)), apply (id_left₂' G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
      apply inv_tr_eq_of_eq_tr,
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' G),
      apply inv_tr_eq_of_eq_tr,
      apply concat, apply (ap (λ x, comp₂ G _ x)), apply (ID₁_respect_inv G),
      apply concat, apply (right_inverse₂' G), do 2 (apply inv_tr_eq_of_eq_tr),
      apply inverse,
      apply concat, apply (transport_eq_transport4 (λ f g h i, two_cell G f g h i)),
      do 10 (apply concat; apply transport4_transport_acc),
      apply transport4_set_reduce, do 4 (apply !homH),
    apply is_hset.elim,
  },
end

exit

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
      fapply nat_trans.mk, intro X, apply (gamma_lambda_transf X),
      intros [X, Y, f], apply (gamma_lambda_transf_nat X Y f),
    fapply @is_iso_nat_trans,
    intro X, esimp, apply (gamma_lambda_transf_iso X),
  apply iso.symm, fapply iso.mk,
    fapply nat_trans.mk, intro G, apply (lambda_gamma_transf G),

end
