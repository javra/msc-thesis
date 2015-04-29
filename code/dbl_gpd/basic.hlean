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

  definition ur_connect (f : hom a b) : D₂ (ID b) f (f⁻¹) (ID b) :=
  thin D (ID b) f (f⁻¹) (ID b) (right_inverse f ⬝ (id_left (ID b))⁻¹)

  definition ur_connect' (f : hom a b) : D₂ (ID a) (f⁻¹) f (ID a) :=
  thin D (ID a) (f⁻¹) f (ID a) (left_inverse f ⬝ (id_left (ID a))⁻¹)

  definition bl_connect (f : hom a b) : D₂ f (ID a) (ID a) (f⁻¹) :=
  thin D f (ID a) (ID a) (f⁻¹) (id_left (ID a) ⬝ (left_inverse f)⁻¹)

  definition bl_connect' (f : hom a b) : D₂ (f⁻¹) (ID b) (ID b) f :=
  thin D (f⁻¹) (ID b) (ID b) f (id_left (ID b) ⬝ (right_inverse f)⁻¹)

  definition bl_connect'_id_eq_ID₁_aux (f f' g h i : hom a a) (p : f = f')
    (comm1 : g ∘ h = i ∘ f) (comm2 : g ∘ h = i ∘ f') :
    p ▹ thin D f g h i comm1 = thin D f' g h i comm2 :=
  begin
    cases p, apply (ap (thin D _ _ _ _)), apply is_hset.elim,
  end

  definition bl_connect'_id_eq_ID₁ :
    bl_connect' (ID a) = (id_inverse a)⁻¹ ▹ ID₁ D (ID a) :=
  begin
    apply eq_inv_tr_of_tr_eq,
    apply concat, rotate 1, apply (thin_id₁ D),
    apply bl_connect'_id_eq_ID₁_aux,
  end


  definition eq_of_thin (pu pv : g ∘ h = i ∘ f)
    (thinu : u = thin D f g h i pu)
    (v : D₂ f g h i) (thinv : v = thin D f g h i pv) : u = v :=
  begin
    apply concat, apply thinu,
    apply inverse, apply concat, apply thinv,
    apply (ap (λ x, thin D f g h i x)),
    apply is_hset.elim,
  end

  --TODO: show that bl_connect and bl_connect' are related...

  end

  section
  parameters {D₀ : Type} [C : groupoid D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type}
    (D : dbl_gpd C D₂)
  include D
  variables ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c)


  definition bl_of_bl_square_aux {a b c d : D₀} {f f' : hom a b} (p : f = f')
    {g g' : hom c d} (q : g = g') {h h' : hom a c} (r : h = h') {i : hom b d}
    (comm1 : g ∘ h = i ∘ f) (comm2 : g' ∘ h' = i ∘ f') :
    p ▹ q ▹ r ▹ (thin D f g h i comm1) = thin D f' g' h' i comm2 :=
  begin
    cases p, cases q, cases r, apply (ap (thin D _ _ _ _) (!is_hset.elim)),
  end

  set_option apply.class_instance true
  definition bl_of_bl_square ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c) :
    (transport (λ x, D₂ x _ _ _) (!comp_inverse)⁻¹
     (transport (λ x, D₂ _ x _ _) (id_left id)
     (transport (λ x, D₂ _ _ x _) (id_left id)
      (comp₁ D (comp₂ D (ID₂ D g) (bl_connect' D g))
       (comp₂ D (bl_connect' D f) (ID₁ D g⁻¹))))))
    = bl_connect' D (g ∘ f) :=
  begin
    do 3 (apply tr_eq_of_eq_inv_tr),
    -- Prove commutativity of second row
    assert line2_commute : (id ∘ id) ∘ id = g ∘ id ∘ g⁻¹,
      apply concat, apply id_right, apply concat, apply id_left,
      apply inverse, apply concat, apply (ap (λ x, _ ∘ x)), apply id_left,
      apply right_inverse,
    -- Prove thinness of second row
    assert line2_thin : comp₂ D (ID₂ D g) (bl_connect' D g)
      = thin D (id ∘ g⁻¹) (id ∘ id) id g line2_commute,
      apply concat, apply (ap (λx, comp₂ D x _)), apply inverse, apply (thin_id₂ D),
      apply (thin_comp₂ D),
    -- Prove commutativity of first row
    assert line1_commute : (id ∘ g⁻¹) ∘ id = f ∘ f⁻¹ ∘ g⁻¹,
      apply concat, apply id_right, apply concat, apply id_left,
      apply inverse, apply concat, apply assoc,
      apply concat, apply (ap (λ x, x ∘ _)), apply right_inverse, apply id_left,
    -- Prove thinness of first row
    assert line1_thin : comp₂ D (bl_connect' D f) (ID₁ D g⁻¹)
      = thin D (f⁻¹ ∘ g⁻¹) (id ∘ g⁻¹) id f line1_commute,
      apply concat, apply (ap (λx, comp₂ D _ x)), apply inverse, apply (thin_id₁ D),
      apply (thin_comp₂ D),
    -- Replace composite squares by thin squares
    apply concat, exact (ap (λx, comp₁ D x _) line2_thin),
    apply concat, exact (ap (λx, comp₁ D _ x) line1_thin),
    -- Thinness of the entire 2x2 grid
    apply concat, apply (thin_comp₁ D),
    apply concat, apply (ap (λ x, _ ∘ x)), apply id_left,
    apply concat, apply id_left,
    apply inverse, apply concat, apply assoc,
    apply concat, apply (ap (λ x, x ∘ _)), apply inverse, apply assoc,
    apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply right_inverse,
    apply concat, apply (ap (λ x, x ∘ _)), apply id_right,
    apply right_inverse,
    do 3 (apply eq_inv_tr_of_tr_eq),
    apply bl_of_bl_square_aux,
  end

  end
end dbl_gpd
