import .decl ..dbl_cat.transports ..thin_structure.basic ..transport4

open eq dbl_precat iso category is_trunc thin_structure

namespace dbl_gpd
  context
  universe variable l
  parameters {D₀ : Type.{l}} [C : groupoid.{l l} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type.{l}}
    (D : dbl_gpd C D₂)
  include D

  variables ⦃a b c d : D₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i)

  definition left_inverse₁' :=
  eq_inv_tr_of_tr_eq _ _ _ _ (eq_inv_tr_of_tr_eq _ _ _ _ (left_inverse₁ D u))

  definition left_inverse₂' :=
  eq_inv_tr_of_tr_eq _ _ _ _ (eq_inv_tr_of_tr_eq _ _ _ _ (left_inverse₂ D u))

  definition right_inverse₁' :=
  eq_inv_tr_of_tr_eq _ _ _ _ (eq_inv_tr_of_tr_eq _ _ _ _ (right_inverse₁ D u))

  definition right_inverse₂' :=
  eq_inv_tr_of_tr_eq _ _ _ _ (eq_inv_tr_of_tr_eq _ _ _ _ (right_inverse₂ D u))

  /-definition comp₁_right_cancel ⦃c₂ d₂ : D₀⦄
    {g₂ : hom c₂ d₂} {h₂ : hom c c₂} {i₂ : hom d d₂}
    {v w : D₂ g g₂ h₂ i₂} (p : comp₁ D v u = comp₁ D w u) : v = w :=
  begin
    apply concat, apply inverse, apply (id_right₁ D),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₁ D _ x)), apply inverse, apply (right_inverse₁ D u),
    apply concat, apply inverse, --apply (transp_comp₁_eq_comp₁_transp_u_r _ v _),
  end-/

  definition ID₁_respect_inv : ID₁ D (f⁻¹) = inv₂ D (ID₁ D f) :=
  sorry

  definition ID₂_respect_inv : ID₂ D (f⁻¹) = inv₁ D (ID₂ D f) :=
  sorry

  definition ID₁_inverse_compose (f : hom a b) :
    comp₂ D (ID₁ D (f⁻¹)) (ID₁ D f) =
    transport (λ x, D₂ _ x id id) ((left_inverse f)⁻¹)
      (transport (λ x, D₂ x _ id id) ((left_inverse f)⁻¹) (ID₁ D (ID a))) :=
  begin
    apply concat, apply (ap (λ x, comp₂ D x _)), apply ID₁_respect_inv,
    apply concat, apply left_inverse₂',
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply inverse, apply concat, apply zero_unique,
    apply inverse, apply concat, apply (transport_eq_transport4 (λ f g h i, D₂ f g h i)),
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply concat, apply transport4_transport_acc,
    apply @transport4_set_reduce,
  end

  definition ur_connect : D₂ (ID b) f (f⁻¹) (ID b) :=
  thin_structure.thin D (ID b) f (f⁻¹) (ID b) (right_inverse f ⬝ (id_left (ID b))⁻¹)

  definition ur_connect' : D₂ (ID a) (f⁻¹) f (ID a) :=
  thin D (ID a) (f⁻¹) f (ID a) (left_inverse f ⬝ (id_left (ID a))⁻¹)

  definition bl_connect : D₂ f (ID a) (ID a) (f⁻¹) :=
  thin D f (ID a) (ID a) (f⁻¹) (id_left (ID a) ⬝ (left_inverse f)⁻¹)

  definition bl_connect' : D₂ (f⁻¹) (ID b) (ID b) f :=
  thin D (f⁻¹) (ID b) (ID b) f (id_left (ID b) ⬝ (right_inverse f)⁻¹)

  --TODO: show that bl_connect and bl_connect' are related...

  end
end dbl_gpd
