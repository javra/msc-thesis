import .decl ..dbl_cat.transports ..thin_structure.basic ..transport4

open eq dbl_precat iso category is_trunc thin_structure

namespace dbl_gpd
  section
  parameters {D₀ : Type} [C : groupoid D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type}
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

  definition ID₁_respect_inv : ID₁ D (f⁻¹) = inv₂ D (ID₁ D f) :=
  begin
    apply concat, apply inverse, apply (id_right₂ D),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₂ _ _ x)),
      apply inverse, apply (right_inverse₂ D (ID₁ D f)),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_b' D),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_l_u' D),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply assoc₂',
    do 2 (apply inv_tr_eq_of_eq_tr),
    apply concat, apply (ap (λ x, comp₂ _ x _)), apply inverse, apply id_comp₂,
    apply concat, apply (ap (λ x, comp₂ _ x _)),
      apply inverse, apply (apD (λ x, ID₁ D x) (left_inverse f)⁻¹),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_r_vert D),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₂ _ x _)), apply zero_unique,
    apply concat, apply (id_left₂' D),
    do 2 (apply inv_tr_eq_of_eq_tr),
    apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, D₂ f g h i)),
    do 8 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

  definition ID₂_respect_inv : ID₂ D (f⁻¹) = inv₁ D (ID₂ D f) :=
  begin
    apply concat, apply inverse, apply (id_right₁ D),
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply concat, apply (ap (λ x, comp₁ _ _ x)),
      apply inverse, apply (right_inverse₁ D (ID₂ D f)),
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_u_r D),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply inverse, apply (transp_comp₁_eq_comp₁_transp_u_l D),
    apply tr_eq_of_eq_inv_tr,
    apply concat, apply assoc₁',
    do 2 (apply inv_tr_eq_of_eq_tr),
    apply concat, apply (ap (λ x, comp₁ _ x _)), apply inverse, apply id_comp₁,
    apply concat, apply (ap (λ x, comp₁ _ x _)),
      apply inverse, apply (apD (λ x, ID₂ D x) (left_inverse f)⁻¹),
    apply concat, apply inverse, apply (transp_comp₂_eq_comp₂_transp_b_horiz D),
    apply inv_tr_eq_of_eq_tr,
    apply concat, apply (ap (λ x, comp₁ _ x _)), apply inverse, apply zero_unique,
    apply concat, apply (id_left₁' D),
    do 2 (apply inv_tr_eq_of_eq_tr),
    apply inverse,
    apply concat, apply (transport_eq_transport4 (λ f g h i, D₂ f g h i)),
    do 8 (apply concat; apply transport4_transport_acc),
    apply transport4_set_reduce,
  end

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
    do 3 (apply concat; apply transport4_transport_acc),
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
