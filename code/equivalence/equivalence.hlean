import algebra.category.adjoint
import .gamma_functor .lambda_functor ..dbl_gpd.basic

open eq category iso is_trunc algebra function xmod Xmod dbl_gpd Dbl_gpd functor
open dbl_precat
open gamma lambda

universe variables l--₁ l₂ l₃

definition gamma_lambda [reducible] := functor.compose gamma.functor.{l l l} lambda.functor.{l l l}

definition gamma_lambda_transf_hom_family [reducible] (X : Xmod)
  (p : carrier (to_fun_ob gamma_lambda X))
  (a : groups (to_fun_ob gamma_lambda X) p) :
  groups X (to_fun_ob (@functor.id (Precategory.mk _ (Xmod.gpd X))) p) :=
lambda_morphism.m (folded_sq.filler a)

definition gamma_lambda_transf [reducible] (X : Xmod) :
  hom (gamma_lambda X) X :=
begin
  fapply xmod_morphism.mk,
    apply functor.id,
    intros, apply gamma_lambda_transf_hom_family, apply a,
    { intros, 
      cases x with [lidx, fillerx],
      cases y with [lidy, fillery],
      esimp[gamma_lambda_transf_hom_family],
      apply concat, apply (lambda_morphism_m_transport_b),
      cases fillerx with [fillerxm, fillerxcomm],
      cases fillery with [fillerym, fillerycomm],
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

definition gamma_lambda_transf_nat (X Y : Xmod.{l l l}) (f : xmod_morphism X Y) :
  ((@functor.id Cat_xmod) f) ∘ (gamma_lambda_transf X)
  = (gamma_lambda_transf Y) ∘ (to_fun_hom gamma_lambda f) :=
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
  hom X (gamma_lambda X) :=
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
  fapply @is_iso.mk, exact (gamma_lambda_transf_inv.{l} X),
  { apply inverse, apply concat, apply (refl (@xmod_morphism.mk _ _ _ _ _ _ _)),
    fapply (xmod_morphism_congr
      (to_fun_ob gamma_lambda X)
      (to_fun_ob gamma_lambda X)),
        apply idp, apply idp,
    esimp, apply eq_of_homotopy, intro p, apply eq_of_homotopy, intro x,
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
    apply eq_of_homotopy, intro p, apply eq_of_homotopy, intro x,
    apply idp,
  },
end

definition inverse_alliso (G : Dbl_gpd) {a b : carrier (gpd G)} (f : hom a b) : is_iso f :=
!all_iso
postfix [parsing-only] `⁻¹ʰ`:std.prec.max_plus := inverse_alliso


section
  parameters (G : Dbl_gpd) ⦃a b c d : carrier (Dbl_gpd.gpd G)⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : two_cell G f g h i)

  private definition all_iso_dgpd [instance] (a b : carrier (Dbl_gpd.gpd G)) (f : hom a b) : is_iso f :=
  !all_iso

  definition lambda_gamma_fold' [reducible] :=
  (comp₂ G (br_connect G i) (comp₂ G u (comp₂ G (bl_connect' G h) (ID₁ G g⁻¹))))

  definition lambda_gamma_fold [reducible] :=
  transport (λ x, two_cell G _ x _ _) (@right_inverse _ _ _ _ _ (!all_iso))
   (transport (λ x, two_cell G _ (_ ∘ x) _ _) (!id_left)
    (transport (λ x, two_cell G _ x _ _) (!id_left)
     lambda_gamma_fold'))

end


section
  variables (G : Dbl_gpd) {a b : carrier (gpd G)} (f : hom a b)

  definition lambda_gamma_transf_aux1 :
    transport (λ x, two_cell G f f (ID a) x) (id_left id)⁻¹ (ID₁ G f)
    = transport (λ x, two_cell G f f x _) (id_left id) (comp₁ G (ID₁ G f) (ID₁ G f)) :=
  begin
    apply inverse, apply tr_eq_of_eq_inv_tr,
    apply (id_left₁' G),
  end

end

section
  variables (G : Dbl_gpd) {a b c d c₂ d₂ : carrier (gpd G)}
    {f : hom a b} {g₁ : hom c d} {h₁ : hom a c} {i₁ : hom b d}
    {g₂ : hom c₂ d₂} {h₂ : hom c c₂} {i₂ : hom d d₂}
    (u : two_cell G f g₁ h₁ i₁)
    (v : two_cell G g₁ g₂ h₂ i₂)

  definition lambda_gamma_transf_aux2_1 :=
  (comp₂ G
       (comp₂ G (ID₁ G i₂)
          (comp₂ G
             (comp₂ G (ID₂ G (ID d))
                (comp₂ G (ID₁ G g₁)
                   (comp₂ G (ID₂ G (ID c)) (ID₁ G (inverse g₁)))))
             (ID₁ G (inverse i₂))))
       (comp₂ G (br_connect G i₂)
          (comp₂ G v (comp₂ G (bl_connect' G h₂) (ID₁ G g₂⁻¹)))))

  check lambda_gamma_transf_aux2_1 G v

--  set_option pp.notation false
  definition lambda_gamma_transf_aux2 :
    (comp₂ G (comp₂ G (br_connect G i₂) (ID₂ G i₂))
       (comp₂ G v (comp₂ G (comp₂ G (ID₂ G h₂) (bl_connect' G h₂)) (ID₁ G g₂⁻¹))))
    = transport4 (λ f g h i, two_cell G f g h i)
    (ap
       (λ (x : hom d c),
          (i₂ ∘ (ID d ∘ g₁ ∘ x) ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse
            h₂ ∘ g₂⁻¹)
       (id_left (inverse g₁)) ⬝ (ap
        (λ (x : hom d c),
           (i₂ ∘ (ID d ∘ g₁ ∘ inverse g₁) ∘ inverse
              i₂) ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
        (id_left (inverse g₁)) ⬝ (ap
         (λ (x : hom d d),
            (i₂ ∘ (ID d ∘ x) ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse
              h₂ ∘ g₂⁻¹)
         (right_inverse g₁) ⬝ (ap
          (λ (x : hom d d),
             (i₂ ∘ (ID d ∘ ID d) ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse
               h₂ ∘ g₂⁻¹)
          (right_inverse g₁) ⬝ (ap
           (λ (x : hom d d),
              (i₂ ∘ x ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
           (id_left (ID d)) ⬝ (ap
            (λ (x : hom d d),
               (i₂ ∘ ID d ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse
                 h₂ ∘ g₂⁻¹)
            (id_left (ID d)) ⬝ (ap
             (λ (x : hom d₂ d),
                (i₂ ∘ x) ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
             (id_left (inverse i₂)) ⬝ (ap
              (λ (x : hom d₂ d),
                 (i₂ ∘ inverse i₂) ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
              (id_left (inverse i₂)) ⬝ (ap
               (λ (x : hom d₂ d₂), x ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
               (right_inverse i₂) ⬝ (ap
                (λ (x : hom d₂ d₂),
                   ID d₂ ∘ i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
                (right_inverse i₂) ⬝ (ap (λ (x : hom d₂ d₂), x)
                 (id_left (i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)) ⬝ (ap
                  (λ (x : hom d₂ d₂), i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
                  (id_left (ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)) ⬝ (ap
                   (λ (x : hom c₂ c₂), i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)
                   (id_left (ID c₂))⁻¹ ⬝ (ap
                    (λ (x : hom c₂ c), i₂ ∘ g₁ ∘ x ∘ g₂⁻¹)
                    (id_left (inverse h₂))⁻¹ ⬝ (ap
                     (λ (x : hom d₂ d₂),
                        i₂ ∘ g₁ ∘ (ID c ∘ inverse h₂) ∘ g₂⁻¹)
                     (id_right (ID d₂))⁻¹ ⬝ ap
                     (λ (w : hom d d₂), w ∘ g₁ ∘ (ID c ∘ inverse h₂) ∘ g₂⁻¹)
                     (id_right i₂)⁻¹)))))))))))))))
    (ap
       (λ (x : hom d c),
          (i₂ ∘ (ID d ∘ g₁ ∘ ID c ∘ inverse g₁) ∘ inverse i₂) ∘ ID
            d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
       (id_left (inverse g₁)) ⬝ (ap
        (λ (x : hom d c),
           (i₂ ∘ (ID d ∘ g₁ ∘ x) ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID
             c₂ ∘ g₂⁻¹)
        (id_left (inverse g₁)) ⬝ (ap
         (λ (x : hom d d),
            (i₂ ∘ (ID d ∘ g₁ ∘ inverse g₁) ∘ inverse i₂) ∘ ID
              d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
         (right_inverse g₁) ⬝ (ap
          (λ (x : hom d d),
             (i₂ ∘ (ID d ∘ x) ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID
               c₂ ∘ g₂⁻¹)
          (right_inverse g₁) ⬝ (ap
           (λ (x : hom d d),
              (i₂ ∘ (ID d ∘ ID d) ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID
                c₂ ∘ g₂⁻¹)
           (id_left (ID d)) ⬝ (ap
            (λ (x : hom d d),
               (i₂ ∘ x ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
            (id_left (ID d)) ⬝ (ap
             (λ (x : hom d₂ d),
                (i₂ ∘ ID d ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
             (id_left (inverse i₂)) ⬝ (ap
              (λ (x : hom d₂ d), (i₂ ∘ x) ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
              (id_left (inverse i₂)) ⬝ (ap
               (λ (x : hom d₂ d₂),
                  (i₂ ∘ inverse i₂) ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
               (right_inverse i₂) ⬝ (ap
                (λ (x : hom d₂ d₂), x ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
                (right_inverse i₂) ⬝ (ap
                 (λ (x : hom d₂ d₂),
                    ID d₂ ∘ ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)
                 (id_left (i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)) ⬝ (ap
                  (λ (x : hom d₂ d₂), x)
                  (id_left (ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)) ⬝ (ap
                   (λ (x : hom c₂ c₂), ID d₂ ∘ g₂ ∘ x ∘ g₂⁻¹)
                   (id_left (ID c₂))⁻¹ ⬝ (ap
                    (λ (x : hom c₂ c),
                       ID d₂ ∘ g₂ ∘ (ID c₂ ∘ ID c₂) ∘ g₂⁻¹)
                    (id_left (inverse h₂))⁻¹ ⬝ (ap
                     (λ (x : hom d₂ d₂),
                        x ∘ g₂ ∘ (ID c₂ ∘ ID c₂) ∘ g₂⁻¹)
                     (id_right (ID d₂))⁻¹ ⬝ ap
                     (λ (w : hom d d₂),
                        comp (comp (ID d₂) (ID d₂))
                          (comp g₂ (comp (comp (ID c₂) (ID c₂)) g₂⁻¹)))
                     (id_right i₂)⁻¹)))))))))))))))
    (ap (λ (x : hom d c), id) (id_left (inverse g₁)) ⬝ (ap (λ (x : hom d c), id)
        (id_left (inverse g₁)) ⬝ (ap (λ (x : hom d d), id) (right_inverse g₁) ⬝ (ap
          (λ (x : hom d d), id)
          (right_inverse g₁) ⬝ (ap (λ (x : hom d d), ID d₂) (id_left (ID d)) ⬝ (ap
            (λ (x : hom d d), ID d₂)
            (id_left (ID d)) ⬝ (ap (λ (x : hom d₂ d), ID d₂)
             (id_left (inverse i₂)) ⬝ (ap (λ (x : hom d₂ d), ID d₂)
              (id_left (inverse i₂)) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
               (right_inverse i₂) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                (right_inverse i₂) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                 (id_left (i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)) ⬝ (ap
                  (λ (x : hom d₂ d₂), ID d₂)
                  (id_left (ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)) ⬝ (ap
                   (λ (x : hom c₂ c₂), ID d₂)
                   (id_left (ID c₂))⁻¹ ⬝ (ap (λ (x : hom c₂ c), ID d₂)
                    (id_left (inverse h₂))⁻¹ ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                     (id_right (ID d₂))⁻¹ ⬝ ap (λ (w : hom d d₂), id)
                     (id_right i₂)⁻¹)))))))))))))))
    (ap (λ (x : hom d c), id) (id_left (inverse g₁)) ⬝ (ap (λ (x : hom d c), id)
        (id_left (inverse g₁)) ⬝ (ap (λ (x : hom d d), id) (right_inverse g₁) ⬝ (ap
          (λ (x : hom d d), id)
          (right_inverse g₁) ⬝ (ap (λ (x : hom d d), ID d₂) (id_left (ID d)) ⬝ (ap
            (λ (x : hom d d), ID d₂)
            (id_left (ID d)) ⬝ (ap (λ (x : hom d₂ d), ID d₂)
             (id_left (inverse i₂)) ⬝ (ap (λ (x : hom d₂ d), ID d₂)
              (id_left (inverse i₂)) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
               (right_inverse i₂) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                (right_inverse i₂) ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                 (id_left (i₂ ∘ g₁ ∘ inverse h₂ ∘ g₂⁻¹)) ⬝ (ap
                  (λ (x : hom d₂ d₂), ID d₂)
                  (id_left (ID d₂ ∘ g₂ ∘ ID c₂ ∘ g₂⁻¹)) ⬝ (ap
                   (λ (x : hom c₂ c₂), ID d₂)
                   (id_left (ID c₂))⁻¹ ⬝ (ap (λ (x : hom c₂ c), ID d₂)
                    (id_left (inverse h₂))⁻¹ ⬝ (ap (λ (x : hom d₂ d₂), ID d₂)
                     (id_right (ID d₂))⁻¹ ⬝ ap (λ (w : hom d d₂), id)
                     (id_right i₂)⁻¹)))))))))))))))
    (lambda_gamma_transf_aux2_1 G v) :=
  begin
    apply concat, apply (ap (λ x, comp₂ G x (comp₂ G v _))), apply (id_right₂' G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ G (br_connect G _) (comp₂ G v (comp₂ G x _)))),
      apply (id_left₂' G),
    apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G _ x))),
      apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' G),
    apply concat, apply (ap (λ x, comp₂ G _ x)),
      apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G _ x))),
      apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' G),
    apply concat, apply (ap (λ x, comp₂ G _ x)),
      apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply (id_left₂ G),
    do 2 (apply tr_eq_of_eq_inv_tr),
    apply concat, apply ap (λ x, comp₂ G x (comp₂ G (br_connect G _) _)),
      apply inverse, apply right_inverse₂ G, apply ID₁ G i₂,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b' G,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_u' G,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply ID₁_respect_inv G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply id_left₂ G,
    apply concat, apply ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b' G,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b' G,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_u' G,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' G),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G x _))
        (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply id_left₂ G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b' G,
    apply concat, apply (ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _))),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b' G,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_b' G,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_r_u' G,
    apply concat, apply (ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _))),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_u' G,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' G),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G (comp₂ G (ID₂ G (ID d)) x) _))
        (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply right_inverse₂ G, apply ID₁ G g₁, esimp,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G x _))
        (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_r_ub G,
    apply concat, apply ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub G,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_ub G,
    do 2 apply tr_eq_of_eq_inv_tr,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G (comp₂ G (ID₂ G (ID d))
        x) _)) (comp₂ G (br_connect G i₂) _)), apply ap (λ x, comp₂ G _ x),
      apply inverse, apply ID₁_respect_inv G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G (comp₂ G (ID₂ G (ID d))
        x) _)) (comp₂ G (br_connect G i₂) _)), apply ap (λ x, comp₂ G _ x),
      apply inverse, apply id_left₂ G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G (comp₂ G (ID₂ G (ID d))
        x) _)) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ (comp₂ G x _))
        (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub G,
    apply concat, apply ap (λ x, comp₂ G (comp₂ G _ x) (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_r_ub G,
    apply concat, apply ap (λ x, comp₂ G x (comp₂ G (br_connect G i₂) _)),
      apply inverse, apply transp_comp₂_eq_comp₂_transp_l_ub G,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_r_ub G,
    do 2 apply tr_eq_of_eq_inv_tr,
    do 12 apply eq_inv_tr_of_tr_eq,
    do 4 apply eq_tr_of_inv_tr_eq,
    apply concat, apply (@transport_eq_transport4 _ _ _ _ (@two_cell G _ _ _ _) _
       (λ w, _) (λ w, (comp (comp (ID d₂) (ID d₂))      
       (comp g₂ (comp (comp (ID c₂) (ID c₂)) (inverse g₂))))) (λ w, id) (λ w, id)),
    do 15 (apply concat; apply transport4_transport_acc), esimp,
  end

exit

end

definition lambda_gamma [reducible] :=
functor.compose lambda.functor.{l l l} gamma.functor.{l l l}

set_option apply.class_instance false
definition lambda_gamma_transf (G : Dbl_gpd) :
  dbl_functor G (lambda_gamma G) :=
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
      apply concat, apply (ap (λ x, comp₂ G x _)), apply (zero_unique G),
      apply concat, apply (id_left₂' G), do 2 (apply tr_eq_of_eq_inv_tr),
      apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G x _))), apply bl_connect'_id_eq_ID₁,
      apply concat, apply (ap (λ x, comp₂ G _ x)), apply inverse,
        apply (transp_comp₂_eq_comp₂_transp_r_u' G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
      apply inv_tr_eq_of_eq_tr,
      apply concat, apply (ap (λ x, comp₂ G _ (comp₂ G x _))), apply (zero_unique G),
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
      apply transport4_set_reduce, do 4 (apply !is_hset_hom),
    apply is_hset.elim,
  },
  { intros,
    fapply lambda_morphism.congr,
      fapply folded_sq.congr,
        apply inverse,
        apply concat, apply (refl (_ ∘ _ ∘ _ ∘ _ ∘ _)),
        apply concat, apply (ap (λ x, x ∘ _)), apply (refl (i₂ ∘ (_ ∘ _) ∘ i₂⁻¹)),
        apply inverse,
        apply concat, apply (ap (λ x, _ ∘ _ ∘ x ∘ _)),
          apply comp_inverse, do 2 (apply !all_iso),
        apply concat, apply inverse, apply assoc,
        apply inverse, apply concat, apply inverse, apply assoc, apply (ap (λ x, _ ∘ x)),
        apply concat, apply inverse, apply assoc,
        apply concat, apply inverse, apply assoc, apply (ap (λ x, _ ∘ x)),
        apply concat, apply inverse, apply assoc, apply (ap (λ x, _ ∘ x)),
        apply concat, apply inverse, apply assoc,
        apply inverse, apply concat, apply inverse, apply assoc, apply (ap (λ x, _ ∘ x)),
        apply inverse, apply concat, apply assoc,
        apply concat, apply assoc,
        apply concat, apply (ap (λ x, x ∘ _)), apply eq.inverse, apply assoc,
        apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply left_inverse,
        apply concat, apply (ap (λ x, x ∘ _)), apply id_right,
        apply concat, apply assoc,
        apply concat, apply (ap (λ x, x ∘ _)), apply left_inverse, apply id_left,
      esimp[lambda_gamma_fold],
      rotate 1, apply is_hset.elim,
      apply eq.inv_tr_eq_of_eq_tr, do 3 (apply tr_eq_of_eq_inv_tr),
      /-apply concat, apply (ap (λ x, comp₂ G x _)), apply inverse, apply br_of_br_square,
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_r G),
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' G),
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ (comp₂ G x _)))),
        apply inverse, apply (bl_of_bl_square G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ x))),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_u' G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) x)),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' G),
      apply inv_tr_eq_of_eq_tr,
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ x))),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_b' G), esimp,
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) x)),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' G),
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ x))),
        apply (transp_comp₂_inner_deal2 G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ (comp₂ G _ x)))),
        apply (lambda_gamma_transf_aux1 G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ x))),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_l G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) x)),
        apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_l G),
      apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_l G),
      apply tr_eq_of_eq_inv_tr,
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) (comp₂ G _ x))),
        apply inverse, apply (interchange G),
      apply concat, apply (ap (λ x, comp₂ G (comp₁ G (comp₂ G (br_connect G i₂) _)
          (comp₂ G _ (br_connect G i₁))) x)), apply inverse, apply (interchange G),
      apply concat, apply inverse, apply (interchange G),
      apply concat,-/
      
  },
end

check @comp₁_row_replacement

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
