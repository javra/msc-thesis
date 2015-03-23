import .gamma_mu_phi ..transport4 ..dbl_gpd.basic ..dbl_cat.transports

open dbl_precat eq iso category is_trunc nat
open equiv sigma sigma.ops prod
open path_algebra dbl_gpd
set_option apply.class_instance false -- disable class instance resolution in the apply tactic
attribute gamma.M [instance]

set_option pp.beta true
namespace gamma
  context
  universe l
  parameters {D₀ : Type.{l}}
    [D₀set : is_hset D₀]
    [C : groupoid.{l l} D₀]
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type.{l})
    [G : dbl_gpd C D₂]
  include G D₀set C

  protected definition gamma_CM1 ⦃x y : D₀⦄ (a : hom x y) (u : M_morphism x) :
    gamma.mu (gamma.phi a u) = a ∘ (gamma.mu u) ∘ (a⁻¹) :=
  idp

  protected definition gamma_CM2_gadget ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  comp₁ D₂ (comp₂ D₂ v (comp₂ D₂ (ID₂ D₂ id) (inv₂ D₂ v)))
    (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ u (ID₁ D₂ (a⁻¹))))

  protected definition right_inverse₂' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (right_inverse₂ D₂ u))

  protected definition gamma_CM2_horizontal ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) (id ∘ w) (id ∘ id) (id ∘ id)) ((id_left _)⁻¹)
    (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) w (id ∘ id) (id ∘ id)) ((comp.right_inverse _)⁻¹)
      (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) id w (id ∘ id)) ((id_left id)⁻¹)
        (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) id id w) ((id_left id)⁻¹)
          (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) w id id) (right_inverse a)
            (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) (a ∘ w) id id) (id_left (a⁻¹))
              (comp₂ D₂ (ID₁ D₂ a) (comp₂ D₂ u (ID₁ D₂ (a⁻¹)))))))))) :=
  begin
    apply concat, apply (ap (λ x, comp₁ D₂ (comp₂ D₂ v x) _)), apply gamma.id_left₂',
    apply concat, apply (ap (λ x, comp₁ D₂ x _)),
      apply (!transp_comp₂_eq_comp₂_transp_l_bu⁻¹),
    apply concat, apply (ap (λ x, comp₁ D₂ x _)),
    apply (ap (λ x, transport.{l l} _ _ x)),
      apply (ap (λ x, transport.{l l} _ _ x)), apply right_inverse₂',
    apply concat, apply (comp₁_transp_eq_comp₁_transp_b (id_left (a⁻¹))),
    apply concat, apply inverse, apply transp_comp₁_eq_comp₁_transp_b_b,
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply comp₁_transp_eq_comp₁_transp_b,
    apply concat, apply inverse, apply transp_comp₁_eq_comp₁_transp_b_b,
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ D₂ x _)), apply inverse, apply zero_unique,
    apply concat, apply gamma.id_left₁',
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply idp,
  end

  protected definition gamma_CM2_horizontal' ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  inv_tr_eq_of_eq_tr _ _ _ _
    (inv_tr_eq_of_eq_tr _ _ _ _
      (tr_eq_of_eq_inv_tr _ _ _ _
        (tr_eq_of_eq_inv_tr _ _ _ _
          (tr_eq_of_eq_inv_tr _ _ _ _
            (tr_eq_of_eq_inv_tr _ _ _ _ (gamma_CM2_horizontal a lidu v u))))))

  protected definition gamma_CM2_vertical ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = (transport (λ (w : hom x x), D₂ (a ∘ (lidu ∘ (a⁻¹))) (id ∘ (id ∘ _)) w (id ∘ id))
       ((id_right id)⁻¹)
       (transport (λ (w : hom x x), D₂ (a ∘ (lidu ∘ (a⁻¹))) (id ∘ (id ∘ _)) id w)
          ((id_right id)⁻¹)
          (comp₂ D₂ v (comp₂ D₂ u (inv₂ D₂ v))))) :=
  begin
    apply concat, apply interchange,
    apply concat, apply (ap (λ x, comp₂ D₂ x _)), apply gamma.id_right₁',
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply interchange,
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ x _)),
      apply (ap (λ x, comp₁ D₂ x _)), apply (!zero_unique⁻¹),
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ x _)),
      apply gamma.id_left₁',
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ _ x)),
      apply gamma.id_right₁',
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply inverse,
      apply transp_comp₂_eq_comp₂_transp_transp_rl,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_transp_rl,
    apply idp,
  end

  protected definition gamma_CM2_vertical' ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  tr_eq_of_eq_inv_tr _ _ _ _
    (tr_eq_of_eq_inv_tr _ _ _ _ (gamma_CM2_vertical a lidu v u))

  protected definition gamma_CM2 ⦃x : D₀⦄ (v u : M_morphism x) :
    gamma.phi (gamma.mu v) u = M_morphism.comp v (M_morphism.comp u (M_morphism.inv v)) :=
  begin
    apply (M_morphism.rec_on v), intros (lidv, fillerv),
    apply (M_morphism.rec_on u), intros (lidu, filleru),
    fapply (M_morphism.congr),
      apply idp,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    unfold M_morphism.filler, unfold M_morphism.comp, unfold M_morphism.inv,
    unfold M_morphism.inv_aux, unfold M_morphism.filler,
    unfold gamma.mu, unfold M_morphism.lid, esimp,
    apply concat, apply inverse, apply gamma_CM2_horizontal', apply fillerv,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply eq_tr_of_inv_tr_eq, apply inverse,
    apply concat, apply inverse, apply (ap (λ x, comp₂ D₂ _ x)),
    apply (ap (λ x, transport.{l l} _ _ x)), apply transp_comp₂_eq_comp₂_transp_l_b,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply transp_comp₂_eq_comp₂_transp_l_b,
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply gamma_CM2_vertical',
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inverse,
    apply concat, apply (@transport_eq_transport4 _ _ _ _ (@D₂ x x x x) (hom x x)
      (λ w, lidv ∘ (lidu ∘ (lidv⁻¹))) (λ w, id ∘ (id ∘ _)) (λ w, w) (λ w, id ∘ id)
      _ _ ((id_right id)⁻¹)),
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
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply transport4_set_reduce,
    apply homH, apply homH, apply homH, apply homH,
  end

  protected definition xmod : xmod (λ x, gamma.M_bundled x) :=
  begin
    fapply xmod.mk,
      exact D₀set,
      intros (x, u), apply (gamma.mu u),
      intros (x, v, u), apply (gamma.mu_respect_comp v u),
      intro x, apply gamma.mu_respect_id,
      intros (x, y, a, u), apply (gamma.phi a u),
      intros (x, u), apply (gamma.phi_respect_id u),
      intros (x, y, z, b, a, u), apply (gamma.phi_respect_P_comp b a u),
      intros (x, y, a, v, u), apply (gamma.phi_respect_M_comp a v u),
      intros (x, y, a, u), apply (gamma_CM1 a u),
      intros (x, v, u), apply (gamma_CM2 v u),
  end

  end

  open Dbl_gpd
  protected definition on_objects (G : Dbl_gpd) : Xmod :=
  Xmod.mk (Groupoid.carrier (gpd G)) (Groupoid.struct (gpd G))
    (λ x, gamma.M_bundled x) (gamma.xmod (two_cell  G))

end gamma
