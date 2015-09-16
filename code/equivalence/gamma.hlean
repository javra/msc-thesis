import .gamma_mu_phi ..transport4 ..dbl_gpd.basic ..dbl_cat.transports ..xmod.decl

open dbl_precat eq iso category is_trunc nat
open equiv sigma sigma.ops prod
open algebra dbl_gpd
set_option apply.class_instance false
attribute gamma.folded_sq_group [instance]

set_option pp.beta true
namespace gamma
  section
  parameters {D₀ : Type}
    [D₀set : is_hset D₀]
    [C : groupoid D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type}
    (G : dbl_gpd C D₂)
  include G D₀set C

  protected definition gamma_CM1 ⦃x y : D₀⦄ (a : hom x y) (u : folded_sq G x) :
    gamma.mu G (gamma.phi G a u) = a ∘ (gamma.mu G u) ∘ (a⁻¹) :=
  idp

  protected definition gamma_CM2_gadget ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  comp₁ G (comp₂ G v (comp₂ G (ID₂ G id) (inv₂ G v)))
    (comp₂ G (ID₁ G a) (comp₂ G u (ID₁ G (a⁻¹))))

  protected definition gamma_CM2_horizontal ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) (id ∘ w) (id ∘ id) (id ∘ id)) ((id_left _)⁻¹)
    (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) w (id ∘ id) (id ∘ id)) ((comp.right_inverse _)⁻¹)
      (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) id w (id ∘ id)) ((id_left id)⁻¹)
        (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) id id w) ((id_left id)⁻¹)
          (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) w id id) (right_inverse a)
            (transport (λ w, D₂ (a ∘ (lidu ∘ (a⁻¹))) (a ∘ w) id id) (id_left (a⁻¹))
              (comp₂ G (ID₁ G a) (comp₂ G u (ID₁ G (a⁻¹)))))))))) :=
  begin
    apply concat, apply (ap (λ x, comp₁ G (comp₂ G v x) _)), apply (id_left₂' G),
    apply concat, apply (ap (λ x, comp₁ G x _)), apply inverse,
      apply (transp_comp₂_eq_comp₂_transp_l_bu G),
    apply concat, apply (ap (λ x, comp₁ G x _)),
    do 2 apply (ap (λ x, transport _ _ x)), apply (right_inverse₂' G),
    apply concat, apply (comp₁_transp_eq_comp₁_transp_b G (id_left (a⁻¹))),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_b G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (comp₁_transp_eq_comp₁_transp_b G),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_b_b G),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ G x _)), apply inverse, apply (zero_unique G),
    apply concat, apply (id_left₁' G),
    do 2 apply eq_tr_of_inv_tr_eq, esimp,
  end

  protected definition gamma_CM2_horizontal' ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  inv_tr_eq_of_eq_tr
    (inv_tr_eq_of_eq_tr
      (tr_eq_of_eq_inv_tr
        (tr_eq_of_eq_inv_tr
          (tr_eq_of_eq_inv_tr
            (tr_eq_of_eq_inv_tr (gamma_CM2_horizontal a lidu v u))))))

  protected definition gamma_CM2_vertical ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = (transport (λ w, D₂ _ _ w _) ((id_right id)⁻¹)
       (transport (λ w, D₂ _ _ _ w) ((id_right id)⁻¹)
          (comp₂ G v (comp₂ G u (inv₂ G v))))) :=
  begin
    apply concat, apply (interchange G),
    apply concat, apply (ap (λ x, comp₂ G x _)), apply (id_right₁' G),
    apply concat, apply (ap (λ x, comp₂ G _ x)), apply (interchange G),
    apply concat, apply (ap (λ x, comp₂ G _ x)), apply (ap (λ x, comp₂ G x _)),
      apply (ap (λ x, comp₁ G x _)), apply inverse, apply (zero_unique G),
    apply concat, apply (ap (λ x, comp₂ G _ x)), apply (ap (λ x, comp₂ G x _)),
      apply (id_left₁' G),
    apply concat, apply (ap (λ x, comp₂ G _ x)), apply (ap (λ x, comp₂ G _ x)),
      apply (id_right₁' G),
    apply concat, apply (ap (λ x, comp₂ G _ x)), apply inverse,
      apply (transp_comp₂_eq_comp₂_transp_transp_rl G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_transp_rl G),
    esimp,
  end

  protected definition gamma_CM2_vertical' ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :=
  tr_eq_of_eq_inv_tr (tr_eq_of_eq_inv_tr (gamma_CM2_vertical a lidu v u))

  protected definition gamma_CM2 ⦃x : D₀⦄ (v u : folded_sq G x) :
    gamma.phi G (gamma.mu G v) u
    = folded_sq.comp G v (folded_sq.comp G u (folded_sq.inv G v)) :=
  begin
    cases v with [lidv, fillerv], cases u with [lidu, filleru],
    fapply (folded_sq.congr), apply idp,
    do 3 apply tr_eq_of_eq_inv_tr,
    unfold folded_sq.filler, unfold folded_sq.comp, unfold folded_sq.inv,
    unfold folded_sq.inv_aux, unfold gamma.mu, esimp,
    apply concat, apply inverse, apply gamma_CM2_horizontal', apply fillerv,
    do 2 apply eq_inv_tr_of_tr_eq, apply eq_tr_of_inv_tr_eq, apply inverse,
    apply concat, apply inverse, apply (ap (λ x, comp₂ G _ x)),
    apply (ap (λ x, transport _ _ x)), apply (transp_comp₂_eq_comp₂_transp_l_b G),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b G),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b G),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply gamma_CM2_vertical',
    do 2 apply tr_eq_of_eq_inv_tr, apply inverse,
    apply concat, apply (@transport_eq_transport4 _ _ _ _ (@D₂ x x x x) (hom x x)
      (λ w, lidv ∘ (lidu ∘ (lidv⁻¹))) (λ w, id ∘ (id ∘ _)) (λ w, w) (λ w, id ∘ id)
      _ _ ((id_right id)⁻¹)),
    do 13 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
    do 4 apply is_hset_hom,
  end

  protected definition xmod [reducible] : xmod (λ x, gamma.folded_sq_Group G x) :=
  begin
    fapply xmod.mk,
      exact D₀set,
      intros [x, u], apply (gamma.mu G u),
      intros [x, v, u], apply (gamma.mu_respect_comp G v u),
      intro x, apply gamma.mu_respect_id,
      intros [x, y, a, u], apply (gamma.phi G a u),
      intros [x, u], apply (gamma.phi_respect_id G u),
      intros [x, y, z, b, a, u], apply (gamma.phi_respect_P_comp G b a u),
      intros [x, y, a, v, u], apply (gamma.phi_respect_M_comp G a v u),
      intros [x, y, a, u], apply (gamma_CM1 a u),
      intros [x, v, u], apply (gamma_CM2 v u),
  end

  end

  open Dbl_gpd
  protected definition on_objects [reducible] (G : Dbl_gpd) : Xmod :=
  Xmod.mk (λ x, gamma.folded_sq_Group G x) (gamma.xmod G)

end gamma
