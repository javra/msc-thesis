import .gamma_mu_phi ..transport4 ..dbl_gpd.basic

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod
open path_algebra dbl_gpd
set_option apply.class_instance false -- disable class instance resolution in the apply tactic
attribute gamma.M [instance]

set_option pp.beta true
namespace gamma
  context
  universe variable l
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

  protected definition compose_inverse₂' ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (compose_inverse₂ D₂ u))

  print definition M_morphism.comp
  protected definition gamma_CM2_horizontal ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = gamma_CM2_gadget a lidu v u :=
  begin
    apply concat, apply (ap (λ x, comp₁ D₂ (comp₂ D₂ v x) _)), apply id_left₂',
    apply concat, apply (ap (λ x, comp₁ D₂ x _)),
      apply (!transp_comp₂_eq_comp₂_transp_l_bu⁻¹),
    apply concat, apply (ap (λ x, comp₁ D₂ x _)),
    apply (ap (λ x, _ ▹ x)), apply (ap (λ x, _ ▹ x)), apply compose_inverse₂',
    apply concat, apply (comp₁_transp_eq_comp₁_transp_b (id_left (a⁻¹))),
    apply concat, apply inverse, apply transp_comp₁_eq_comp₁_transp_b_b,
    apply moveR_transport_V,
    apply concat, apply comp₁_transp_eq_comp₁_transp_b,
    apply concat, apply inverse, apply transp_comp₁_eq_comp₁_transp_b_b,
    apply moveR_transport_V,
    apply concat, apply (ap (λ x, comp₁ D₂ x _)), apply inverse, apply zero_unique,
    apply concat, apply id_left₁',
    --apply moveR_transport_V, apply moveR_transport_V, apply moveR_transport_p,
    --apply moveR_transport_p,
    apply moveL_transport_p, apply moveL_transport_p,
  end

  check id_left₁'
  protected definition gamma_CM2_vertical ⦃x : D₀⦄ (a lidu : hom x x)
    (v : D₂ a id id id) (u : D₂ lidu id id id) :
  gamma_CM2_gadget a lidu v u
  = gamma_CM2_gadget a lidu v u :=
  begin
    apply concat, apply interchange,
    apply concat, apply (ap (λ x, comp₂ D₂ x _)), apply id_right₁',
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply interchange,
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ x _)),
      apply (ap (λ x, comp₁ D₂ x _)), apply (!zero_unique⁻¹),
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ x _)),
      apply id_left₁',
    apply concat, apply (ap (λ x, comp₂ D₂ _ x)), apply (ap (λ x, comp₂ D₂ _ x)),
      apply id_right₁',
  end

  protected definition gamma_CM2 ⦃x : D₀⦄ (v u : M_morphism x) :
    phi (mu v) u = M_morphism.comp v (M_morphism.comp u (M_morphism.inv v)) :=
  begin
    apply (M_morphism.rec_on v), intros (lidv, fillerv),
    apply (M_morphism.rec_on u), intros (lidu, filleru),
    fapply (M_morphism.congr),
      apply idp,
    apply moveR_transport_p, apply moveR_transport_p, apply moveR_transport_p,
    unfold M_morphism.filler, unfold M_morphism.comp, unfold M_morphism.inv, esimp,
  end

  end
end gamma
