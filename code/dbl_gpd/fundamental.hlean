import algebra.groupoid ..transport4
import .decl

open eq iso category dbl_precat is_trunc nat sigma sigma.ops

namespace dbl_gpd
  variables {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
  include Xtrunc Atrunc Cset

  definition square_rec_on {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i)
    {P : Π (a b c d : X) (f : a = b) (g : c = d) (h : a = c) (i : b = d),
       h ⬝ g = f ⬝ i → Type}
    (H : P a a a a idp idp idp idp idp) : P a b c d f g h i u :=
  begin
    revert u, revert f, revert h, revert g, apply (eq.rec_on i),
    intro g, apply (eq.rec_on g),
    intros, apply (eq.rec_on u),
    apply (eq.rec_on h), exact H,
  end

  definition fundamental_groupoid [reducible] : groupoid C :=
  groupoid.mk
    (λ (a b : C), ι a =  ι b)
    (λ (a b : C), have ish : is_hset (ι a = ι b),
      from is_trunc_eq nat.zero (ι a) (ι b), ish)
    (λ (a b c : C) (p : ι b = ι c) (q : ι a = ι b), q ⬝ p)
    (λ (a : C), refl (ι a))
    (λ (a b c d : C) (p : ι c = ι d) (q : ι b = ι c) (r : ι a = ι b), con.assoc r q p)
    (λ (a b : C) (p : ι a = ι b), con_idp p)
    (λ (a b : C) (p : ι a = ι b), idp_con p)
    (λ ⦃a b : C⦄ (p : ι a = ι b),
      @is_iso.mk C _ a b p (eq.inverse p) (!con.right_inv) (!con.left_inv))

  --FLAT VERSIONS
  definition fund_dbl_precat_flat_comp₁ {a₁ b₁ a₂ b₂ a₃ b₃ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    (h₁ ⬝ h₂) ⬝ g₂ = f₁ ⬝ (i₁ ⬝ i₂) :=
  calc (h₁ ⬝ h₂) ⬝ g₂ = h₁ ⬝ (h₂ ⬝ g₂) : by rewrite con.assoc
                 ... = h₁ ⬝ (g₁ ⬝ i₂) : by rewrite v
                 ... = (h₁ ⬝ g₁) ⬝ i₂ : by rewrite con.assoc'
                 ... = (f₁ ⬝ i₁) ⬝ i₂ : by rewrite u
                 ... = f₁ ⬝ (i₁ ⬝ i₂) : by rewrite con.assoc

  definition fund_dbl_precat_flat_inv₁ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    h⁻¹ ⬝ f = g ⬝ i⁻¹ :=
  begin
    apply inv_con_eq_of_eq_con,
    apply inverse, apply concat, apply inverse, apply con.assoc,
    apply con_inv_eq_of_eq_con, exact u,
  end

  definition fund_dbl_precat_flat_comp₂ {a₁ a₂ a₃ b₁ b₂ b₃ : X}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    (v : i₁ ⬝ g₂ = f₂ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    h₁ ⬝ (g₁ ⬝ g₂) = (f₁ ⬝ f₂) ⬝ i₂ :=
  calc h₁ ⬝ (g₁ ⬝ g₂) = (h₁ ⬝ g₁) ⬝ g₂ : by rewrite con.assoc'
                 ... = (f₁ ⬝ i₁) ⬝ g₂ : by rewrite u
                 ... = f₁ ⬝ (i₁ ⬝ g₂) : by rewrite con.assoc
                 ... = f₁ ⬝ (f₂ ⬝ i₂) : by rewrite v
                 ... = (f₁ ⬝ f₂) ⬝ i₂ : by rewrite con.assoc'

  definition fund_dbl_precat_flat_inv₂ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    i ⬝ g⁻¹ = f⁻¹ ⬝ h :=
  begin
    apply con_inv_eq_of_eq_con,
    apply inverse, apply concat, apply con.assoc,
    apply inv_con_eq_of_eq_con, exact u,
  end

  definition fund_dbl_precat_flat_assoc₁ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    {g₃ : a₄ = b₄} {h₃ : a₃ = a₄} {i₃ : b₃ = b₄}
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    con.assoc i₁ i₂ i₃ ▹ con.assoc h₁ h₂ h₃ ▹
      (fund_dbl_precat_flat_comp₁ w (fund_dbl_precat_flat_comp₁ v u))
    = fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₁ w v) u :=
  begin
    revert u, revert f₁, revert h₁, revert i₁,
    revert v, revert g₁, revert h₂, revert i₂,
    revert w, revert g₂, revert h₃, revert g₃, cases i₃,
    intro g₃, cases g₃,
    intros [h₃, g₂, w], apply (eq.rec_on w),
    cases h₃,
    intro i₂, cases i₂,
    intros [h₂, g₁, v], apply (eq.rec_on v),
    apply (eq.rec_on h₂),
    intro i₁, cases i₁,
    intros [h₁, g₁, u], apply (eq.rec_on u),
    cases h₁,
    apply idp,
  end

  definition fund_dbl_precat_flat_assoc₂ {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : X}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    {f₃ : a₃ = a₄} {g₃ : b₃ = b₄} {i₃ : a₄ = b₄}
    (w : i₂ ⬝ g₃ = f₃ ⬝ i₃)
    (v : i₁ ⬝ g₂ = f₂ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    con.assoc g₁ g₂ g₃ ▹ con.assoc f₁ f₂ f₃ ▹
      (fund_dbl_precat_flat_comp₂ w (fund_dbl_precat_flat_comp₂ v u))
    = fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_comp₂ w v) u :=
  begin
    revert v,
    revert w, revert f₃, revert f₂, revert i₃, revert i₂,
    revert u, revert h₁, revert i₁,
    revert g₃, revert g₂, revert g₁,
    intro g₁, cases g₁,
    intro g₂, cases g₂,
    intro g₃, cases g₃,
    intro i₁, cases i₁,
    intro h₁, intro u, apply (eq.rec_on u),
    apply (eq.rec_on h₁),
    intro i₂, cases i₂,
    intro i₃, cases i₃,
    intro f₂, intro f₃,
    intro w, apply (eq.rec_on w),
    intro v, apply (eq.rec_on v),
    apply idp,
  end

  definition fund_dbl_precat_flat_assoc₁' {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    {g₃ : a₄ = b₄} {h₃ : a₃ = a₄} {i₃ : b₃ = b₄}
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_assoc₁ w v u))

  definition fund_dbl_precat_flat_assoc₂' {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : X}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    {f₃ : a₃ = a₄} {g₃ : b₃ = b₄} {i₃ : a₄ = b₄}
    (w : i₂ ⬝ g₃ = f₃ ⬝ i₃)
    (v : i₁ ⬝ g₂ = f₂ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_assoc₂ w v u))

  definition fund_dbl_precat_flat_id₁ {a b : X} (g : a = b) :
    refl a ⬝ g = g ⬝ refl b :=
  idp_con g

  definition fund_dbl_precat_flat_id₂ {a b : X} (g : a = b) :
    g ⬝ refl b = refl a ⬝ g :=
  (idp_con g)⁻¹

  definition fund_dbl_precat_flat_id₁_left {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_id₁ g) u = u :=
  begin
    cases g, cases i, cases u, apply idp,
  end

  definition fund_dbl_precat_flat_id₂_left {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_id₂ i) u = u :=
  begin
    cases i, cases g, cases u, apply idp,
  end

  definition fund_dbl_precat_flat_id₁_right {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    transport (λ x, _ = _ ⬝ x) (!idp_con)
      (transport (λ x, x ⬝ _ = _) (!idp_con)
        (fund_dbl_precat_flat_comp₁ u (fund_dbl_precat_flat_id₁ f)))
    = u :=
  begin
    cases g, cases i, cases h, cases u, apply idp,
  end

  definition fund_dbl_precat_flat_id₂_right {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    transport (λ x, _ ⬝ x = _) (!idp_con)
      (transport (λ x, _ = x ⬝ _) (!idp_con)
        (fund_dbl_precat_flat_comp₂ u (fund_dbl_precat_flat_id₂ h))) = u :=
  begin
    revert u, revert f, revert g, revert h,
    cases i,
    intro h, cases h,
    intro f, cases f,
    intro g, apply (eq.rec_on g),
    intro u, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_id₁_right'  {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_id₁_right u))

  definition fund_dbl_precat_flat_id₂_right'  {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_id₂_right u))

  definition fund_dbl_precat_flat_left_inverse₁ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
  transport (λ x, _ = f ⬝ x) (con.right_inv i)
    (transport (λ x, x ⬝ _ = _) (con.right_inv h)
      (fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_inv₁ u) u))
  = idp_con f :=
  begin
    revert u, revert f, revert g, revert h,
    cases i,
    intro h, cases h,
    intro f, cases f,
    intro g, apply (eq.rec_on g),
    intro u, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_right_inverse₁ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
  transport (λ x, _ = _ ⬝ x) (con.left_inv i)
    (transport (λ x, x ⬝ _ = _) (con.left_inv h)
      (fund_dbl_precat_flat_comp₁ u (fund_dbl_precat_flat_inv₁ u)))
  = idp_con g :=
  begin
    revert u, revert f, revert g, revert h,
    cases i,
    intro h, cases h,
    intro f, cases f,
    intro g, apply (eq.rec_on g),
    intro u, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_left_inverse₂ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
  transport (λ x, _ ⬝ x = _) (con.right_inv g)
    (transport (λ x, _ = x ⬝ _) (con.right_inv f)
      (fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_inv₂ u) u))
  = (idp_con h)⁻¹ :=
  begin
    revert u, revert f, revert g, revert h,
    cases i,
    intro h, cases h,
    intro f, cases f,
    intro g, apply (eq.rec_on g),
    intro u, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_right_inverse₂ {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
  transport (λ x, _ ⬝ x = _) (con.left_inv g)
    (transport (λ x, _ = x ⬝ _) (con.left_inv f)
      (fund_dbl_precat_flat_comp₂ u (fund_dbl_precat_flat_inv₂ u)))
  = (idp_con i)⁻¹ :=
  begin
    revert u, revert f, revert g, revert h,
    cases i,
    intro h, cases h,
    intro f, cases f,
    intro g, apply (eq.rec_on g),
    intro u, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_left_inverse₁' {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_left_inverse₁ u))

  definition fund_dbl_precat_flat_right_inverse₁' {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_right_inverse₁ u))

  definition fund_dbl_precat_flat_left_inverse₂' {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_left_inverse₂ u))

  definition fund_dbl_precat_flat_right_inverse₂'  {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (fund_dbl_precat_flat_right_inverse₂ u))

  section
  variables
    {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : X}
    {f₀₀ : a₀₀ = a₀₁} {f₀₁ : a₀₁ = a₀₂} {f₁₀ : a₁₀ = a₁₁} {f₁₁ : a₁₁ = a₁₂}
    {f₂₀ : a₂₀ = a₂₁} {f₂₁ : a₂₁ = a₂₂} {g₀₀ : a₀₀ = a₁₀} {g₀₁ : a₀₁ = a₁₁}
    {g₀₂ : a₀₂ = a₁₂} {g₁₀ : a₁₀ = a₂₀} {g₁₁ : a₁₁ = a₂₁} {g₁₂ : a₁₂ = a₂₂}
    (x : g₁₁ ⬝ f₂₁ = f₁₁ ⬝ g₁₂) (w : g₁₀ ⬝ f₂₀ = f₁₀ ⬝ g₁₁)
    (v : g₀₁ ⬝ f₁₁ = f₀₁ ⬝ g₀₂) (u : g₀₀ ⬝ f₁₀ = f₀₀ ⬝ g₀₁)

  definition fund_dbl_precat_flat_interchange_vert_horiz :=
    fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_comp₁ x v)
      (fund_dbl_precat_flat_comp₁ w u)

  definition fund_dbl_precat_flat_interchange_horiz_vert :=
    fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₂ x w)
      (fund_dbl_precat_flat_comp₂ v u)

  definition fund_dbl_precat_flat_interchange :
    fund_dbl_precat_flat_interchange_vert_horiz x w v u
    = fund_dbl_precat_flat_interchange_horiz_vert x w v u :=
  begin
    revert v, revert f₀₁, revert g₀₂,
    revert u, revert f₀₀, revert g₀₁, revert g₀₀,
    revert x, revert f₁₁, revert g₁₂, revert f₂₁,
    revert w, revert f₁₀, revert g₁₁, revert g₁₀,
    cases f₂₀,
    intro g₁₀, cases g₁₀,
    intro g₁₁, cases g₁₁,
    intro f₁₀, intro w, apply (eq.rec_on w),
    intro f₂₁, cases f₂₁,
    intro g₁₂, cases g₁₂,
    intro f₁₁, intro x, apply (eq.rec_on x),
    intro g₀₀, cases g₀₀,
    intro g₀₁, cases g₀₁,
    intro f₀₀, intro u, apply (eq.rec_on u),
    intro g₀₂, cases g₀₂,
    intro f₀₁, apply (eq.rec_on f₀₁),
    intro v,   apply (eq.rec_on v),
    apply idp,
  end

  end

end dbl_gpd

--NON-FLAT VERSIONS
namespace dbl_gpd
  definition fund_dbl_precat_comp₁ [reducible] {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
    {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {f₁ : ι a₁ = ι b₁} {g₁ : ι a₂ = ι b₂} {h₁ : ι a₁ = ι a₂} {i₁ : ι b₁ = ι b₂}
    {g₂ : ι a₃ = ι b₃} {h₂ : ι a₂ = ι a₃} {i₂ : ι b₂ = ι b₃}
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      ap ι' (h₁ ⬝ h₂) ⬝ ap ι' g₂ = ap ι' f₁ ⬝ ap ι' (i₁ ⬝ i₂) :=
  ((ap_con ι' i₁ i₂)⁻¹) ▹ ((ap_con ι' h₁ h₂)⁻¹) ▹
  @fund_dbl_precat_flat_comp₁ X A C Xtrunc Atrunc Cset
    (ι' (ι a₁)) (ι' (ι b₁)) (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₃)) (ι' (ι b₃))
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
    (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) v u

  definition fund_dbl_precat_inv₁ [reducible] {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
    {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    ap ι' h⁻¹ ⬝ ap ι' f = ap ι' g ⬝ ap ι' i⁻¹ :=
  ((ap_inv ι' i)⁻¹) ▹  ((ap_inv ι' h)⁻¹) ▹
  @fund_dbl_precat_flat_inv₁ X A C Xtrunc Atrunc Cset
    (ι' (ι a)) (ι' (ι b)) (ι' (ι c)) (ι' (ι d))
    (ap ι' f) (ap ι' g) (ap ι' h) (ap ι' i) u

  definition fund_dbl_precat_inv₂ [reducible] {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
    {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    ap ι' i ⬝ ap ι' g⁻¹ = ap ι' f⁻¹ ⬝ ap ι' h :=
  ((ap_inv ι' g)⁻¹) ▹  ((ap_inv ι' f)⁻¹) ▹
  @fund_dbl_precat_flat_inv₂ X A C Xtrunc Atrunc Cset
    (ι' (ι a)) (ι' (ι b)) (ι' (ι c)) (ι' (ι d))
    (ap ι' f) (ap ι' g) (ap ι' h) (ap ι' i) u

  --HALF-FlAT VERSION FOR THE INTERCHANGE LAW
  context
  parameters (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X}
    {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : A}
    {f₀₀ : a₀₀ = a₀₁} {f₀₁ : a₀₁ = a₀₂}
    {f₁₀ : a₁₀ = a₁₁} {f₁₁ : a₁₁ = a₁₂}
    {f₂₀ : a₂₀ = a₂₁} {f₂₁ : a₂₁ = a₂₂}
    {g₀₀ : a₀₀ = a₁₀} {g₀₁ : a₀₁ = a₁₁}
    {g₀₂ : a₀₂ = a₁₂} {g₁₀ : a₁₀ = a₂₀}
    {g₁₁ : a₁₁ = a₂₁} {g₁₂ : a₁₂ = a₂₂}
    (x : ap ι' g₁₁ ⬝ ap ι' f₂₁ = ap ι' f₁₁ ⬝ ap ι' g₁₂)
    (w : ap ι' g₁₀ ⬝ ap ι' f₂₀ = ap ι' f₁₀ ⬝ ap ι' g₁₁)
    (v : ap ι' g₀₁ ⬝ ap ι' f₁₁ = ap ι' f₀₁ ⬝ ap ι' g₀₂)
    (u : ap ι' g₀₀ ⬝ ap ι' f₁₀ = ap ι' f₀₀ ⬝ ap ι' g₀₁)
  include Xtrunc Atrunc Cset

  definition fund_dbl_precat_interchange_aux :
    (fund_dbl_precat_flat_comp₁
       (transport (λ a_0, _ ⬝ a_0 = _) ((ap_con ι' f₂₀ f₂₁)⁻¹)
          (transport (λ a_1, _ = a_1 ⬝ _) ((ap_con ι' f₁₀ f₁₁)⁻¹)
             (fund_dbl_precat_flat_comp₂ x w)))
       (transport (λ a_0, _ ⬝ a_0 = _) ((ap_con ι' f₁₀ f₁₁)⁻¹)
          (transport (λ a_1, _ = a_1 ⬝ _) ((ap_con ι' f₀₀ f₀₁)⁻¹)
             (fund_dbl_precat_flat_comp₂ v u))))
    = ((ap_con ι' f₂₀ f₂₁)⁻¹) ▹ ((ap_con ι' f₀₀ f₀₁)⁻¹) ▹
      (fund_dbl_precat_flat_comp₁
        (fund_dbl_precat_flat_comp₂ x w)
        (fund_dbl_precat_flat_comp₂ v u)) :=
  begin
    reverts [g₀₀, g₀₁, g₀₂, g₁₀, g₁₁, g₁₂, u, v, w, x],
    reverts [f₀₁, f₁₁, f₂₁],
    cases f₀₀, cases f₁₀, cases f₂₀,
    intros [f₀₁, f₁₁, f₂₁],
    cases f₀₁, cases f₁₁, cases f₂₁,
    intros, apply idp,
  end
exit
  definition fund_dbl_precat_interchange_aux2 :
    (fund_dbl_precat_flat_comp₂
       (transport (λ a_1, _ = _ ⬝ a_1) ((ap_con ι' g₀₂ g₁₂)⁻¹)
          (transport (λ a_0, a_0 ⬝ _ = _) ((ap_con ι' g₀₁ g₁₁)⁻¹)
             (fund_dbl_precat_flat_comp₁ x v)))
       (transport (λ a_1, _ = _ ⬝ a_1) ((ap_con ι' g₀₁ g₁₁)⁻¹)
          (transport (λ a_0, a_0 ⬝ _ = _) ((ap_con ι' g₀₀ g₁₀)⁻¹)
             (fund_dbl_precat_flat_comp₁ w u))))
    = ((ap_con ι' g₀₂ g₁₂)⁻¹) ▹ ((ap_con ι' g₀₀ g₁₀)⁻¹) ▹
      (fund_dbl_precat_flat_comp₂
        (fund_dbl_precat_flat_comp₁ x v)
        (fund_dbl_precat_flat_comp₁ w u)) :=
  begin
    reverts [f₀₀, f₁₀, f₂₀, f₀₁, f₁₁, f₂₁, u, v, w, x],
    reverts [g₁₀, g₁₁, g₁₂],
    cases g₀₀, cases g₀₁, cases g₀₂,
    intros [g₁₀, g₁₁, g₁₂],
    cases g₁₀, cases g₁₁, cases g₁₂,
    intros, apply idp,
  end

  definition fund_dbl_precat_interchange_aux3 :
    (transport (λ a_6, a_6 ⬝ _ = _) (ap_con ι' g₀₀ g₁₀)
     (transport (λ a_6, _ = _ ⬝ a_6) (ap_con ι' g₀₂ g₁₂)
      (transport (λ x, _ = x ⬝ _) (ap_con ι' f₀₀ f₀₁)
       (transport (λ x, _ ⬝ x = _) (ap_con ι' f₂₀ f₂₁)
        (transport (λ x, _ = _ ⬝ x) ((ap_con ι' g₀₂ g₁₂)⁻¹)
         (transport (λ x, x ⬝ _ = _) ((ap_con ι' g₀₀ g₁₀)⁻¹)
          (transport (λ x, _ ⬝ x = _) ((ap_con ι' f₂₀ f₂₁)⁻¹)
           (transport (λ x, _ = x ⬝ _) ((ap_con ι' f₀₀ f₀₁)⁻¹)
            (fund_dbl_precat_flat_interchange_vert_horiz x w v u)))))))))
   = (fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_comp₁ x v)
       (fund_dbl_precat_flat_comp₁ w u)) :=
  begin
    reverts [u, v, w, x],
    reverts [f₁₀, f₁₁, g₀₁, g₁₁],
    reverts [f₂₀, f₂₁],
    reverts [g₀₂, g₁₂],
    reverts [g₀₀, g₁₀],
    revert f₀₁, cases f₀₀,
    intro f₀₁, cases f₀₁,
    intro g₀₀, cases g₀₀,
    intro g₁₀, cases g₁₀,
    intro g₀₂, cases g₀₂,
    intro g₁₂, cases g₁₂,
    intro f₂₀, cases f₂₀,
    intros,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply idp,
  end

  end

  --DEFINITIONS FOR THE VERTICAL WORM PRECATEGORY
  context
  parameters (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    (ι' : A → X) (ι : C → A)
    {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    {f₁ : ι a₁ = ι b₁} {g₁ : ι a₂ = ι b₂} {h₁ : ι a₁ = ι a₂} {i₁ : ι b₁ = ι b₂}
    {g₂ : ι a₃ = ι b₃} {h₂ : ι a₂ = ι a₃} {i₂ : ι b₂ = ι b₃}
    {g₃ : ι a₄ = ι b₄} {h₃ : ι a₃ = ι a₄} {i₃ : ι b₃ = ι b₄}
    (w : ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₂ ⬝ ap ι' i₃)
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁)
  include Xtrunc Atrunc Cset

  definition fund_dbl_precat_flat_transp1
    (vu : ap ι' (h₁ ⬝ h₂) ⬝ ap ι' g₂ = ap ι' f₁ ⬝ (ap ι' i₁ ⬝ ap ι' i₂)) :
  fund_dbl_precat_flat_comp₁ w
    (transport (λ a_1, (ap ι' (h₁ ⬝ h₂)) ⬝ (ap ι' g₂) = (ap ι' f₁) ⬝ a_1)
    ((ap_con ι' i₁ i₂)⁻¹) vu)
  = transport (λ a_1, _) ((ap_con ι' i₁ i₂)⁻¹) (fund_dbl_precat_flat_comp₁ w vu) :=
  begin
    apply (eq.rec_on ((ap_con ι' i₁ i₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp2
    (vu : ap ι' h₁ ⬝ ap ι' h₂ ⬝ ap ι' g₂ = ap ι' f₁ ⬝ (ap ι' i₁ ⬝ ap ι' i₂)) :
  fund_dbl_precat_flat_comp₁ w (transport (λ x, x ⬝ _ = _) ((ap_con ι' h₁ h₂)⁻¹) vu)
  = transport (λ x, _) ((ap_con ι' h₁ h₂)⁻¹) (fund_dbl_precat_flat_comp₁ w vu) :=
  begin
    apply (eq.rec_on ((ap_con ι' h₁ h₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp3
    (wv : ap ι' (h₂ ⬝ h₃) ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, _ = _ ⬝ x) ((ap_con ι' i₂ i₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_con ι' i₂ i₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_con ι' i₂ i₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp4
    (wv : ap ι' h₂ ⬝ ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, x ⬝ _ = _) ((ap_con ι' h₂ h₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_con ι' h₂ h₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_con ι' h₂ h₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_assoc₁_aux {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : A}
    (f₁ : a₁ = b₁) (g₁ : a₂ = b₂) (h₁ : a₁ = a₂) (i₁ : b₁ = b₂)
    (g₂ : a₃ = b₃) (h₂ : a₂ = a₃) (i₂ : b₂ = b₃) (g₃ : a₄ = b₄)
    (h₃ : a₃ = a₄) (i₃ : b₃ = b₄)
    (w : (ap ι' h₃) ⬝ (ap ι' g₃) = (ap ι' g₂) ⬝ (ap ι' i₃))
    (v : (ap ι' h₂) ⬝ (ap ι' g₂) = (ap ι' g₁) ⬝ (ap ι' i₂))
    (u : (ap ι' h₁) ⬝ (ap ι' g₁) = (ap ι' f₁) ⬝ (ap ι' i₁)) :
    (transport (λ a_6, ((ap ι' h₁) ⬝ a_6) ⬝ (ap ι' g₃) = _) (ap_con ι' h₂ h₃)
     (transport (λ a_6, _ =  ((ap ι' f₁) ⬝ ((ap ι' i₁) ⬝ a_6))) (ap_con ι' i₂ i₃)
      (transport (λ a_6, (a_6 ⬝ (ap ι' g₃)) = _) (ap_con ι' h₁ (concat h₂ h₃))
       (transport (λ a_6, _ = (ap ι' f₁) ⬝ a_6) (ap_con ι' i₁ (concat i₂ i₃))
        (transport (λ a_6, _ = (ap ι' f₁) ⬝ (ap ι' a_6)) (con.assoc i₁ i₂ i₃)
         (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g₃) = _) (con.assoc h₁ h₂ h₃)
          (transport (λ a_6, _ =  (ap ι' f₁) ⬝ a_6) ((ap_con ι' (concat i₁ i₂) i₃)⁻¹)
           (transport (λ a_6, a_6 ⬝ (ap ι' g₃) = _) ((ap_con ι' (concat h₁ h₂) h₃)⁻¹)
            (transport (λ a_6, _ = (ap ι' f₁) ⬝ (a_6 ⬝ (ap ι' i₃))) ((ap_con ι' i₁ i₂)⁻¹)
             (transport (λ a_6, (a_6 ⬝ (ap ι' h₃)) ⬝ (ap ι' g₃) = _) ((ap_con ι' h₁ h₂)⁻¹)
              (transport (λ a_0, a_0 ⬝  (ap ι' g₃) = _)
                ((con.assoc (ap ι' h₁) (ap ι' h₂) (ap ι' h₃))⁻¹)
                (transport (λ a_0, _ = (ap ι' f₁) ⬝ a_0)
                   ((con.assoc (ap ι' i₁) (ap ι' i₂) (ap ι' i₃))⁻¹)
                   (fund_dbl_precat_flat_comp₁
                     (fund_dbl_precat_flat_comp₁ w v) u)))))))))))))
     = (fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₁ w v) u) :=
  begin
    reverts [u, v, w],
    revert g₃, revert i₃, revert h₃,
    revert g₂, revert i₂, revert h₂,
    revert g₁, revert i₁, revert h₁,
    intro h₁, cases h₁,
    intro i₁, cases i₁,
    intro g₁,
    intro h₂, cases h₂,
    intro i₂, cases i₂,
    intro g₂,
    intro h₃, cases h₃,
    intro i₃, cases i₃,
    intros, apply idp,
  end

  definition fund_dbl_precat_assoc₁ :
    (con.assoc i₁ i₂ i₃) ▹ (con.assoc h₁ h₂ h₃) ▹
      (fund_dbl_precat_comp₁ w (fund_dbl_precat_comp₁ v u))
    = fund_dbl_precat_comp₁ (fund_dbl_precat_comp₁ w v) u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp1, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp2, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_assoc₁',
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply inverse,
    apply concat, apply fund_dbl_precat_flat_transp3, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp4, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_assoc₁_aux,
  end

  definition fund_dbl_precat_id₁ [reducible] {a b : C} (f : ι a = ι b) :
    ap ι' (refl (ι a)) ⬝ ap ι' f = ap ι' f ⬝ ap ι' (refl (ι b)) :=
  idp_con (ap ι' f)

  definition fund_dbl_precat_id₁_left_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝ (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (ap_con ι' h (refl c))
      (transport (λ a_6, _ = (ap ι' f) ⬝ a_6) (ap_con ι' i (refl d))
        (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g) = _) ((con_idp h)⁻¹)
          (transport (λ a_6,  _ = (ap ι' f) ⬝ (ap ι' a_6)) ((con_idp i)⁻¹) u))))
    = u :=
  begin
    cases i, cases h, apply idp,
  end

  definition fund_dbl_precat_id₁_left (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝ (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (con_idp i)
     (transport (λ a_4, (ap ι' a_4) ⬝ (ap ι' g) = _) (con_idp h)
       (fund_dbl_precat_comp₁ (fund_dbl_precat_id₁ g) u)) = u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_id₁_left,
    apply inverse, apply fund_dbl_precat_id₁_left_aux,
  end

  definition fund_dbl_precat_id₁_right_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, _ =  (ap ι' f) ⬝ a_6) (idp_con (ap ι' i))
      (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (idp_con (ap ι' h))
        (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (ap_con ι' (refl a) h)
          (transport (λ a_6, _ = (ap ι' f) ⬝ a_6) (ap_con ι' (refl b) i)
            (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g) = _) ((idp_con h)⁻¹)
              (transport (λ a_6, _ = (ap ι' f) ⬝ (ap ι' a_6)) ((idp_con i)⁻¹) u))))))
     = u :=
  begin
    revert u,
    revert g, revert i, revert h,
    intro h, cases h,
    intro i, cases i,
    intros, apply idp,
  end

  definition fund_dbl_precat_id₁_right (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝ (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (idp_con i)
      (transport (λ a_3, (ap ι' a_3) ⬝ (ap ι' g) = _) (idp_con h)
        (fund_dbl_precat_comp₁ u (fund_dbl_precat_id₁ f))))
    = u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_id₁_right',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_id₁_right_aux,
  end

  end

  definition fund_dbl_precat_comp₂ {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc: is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
    {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {f₁ : ι a₁ = ι a₂} {g₁ : ι b₁ = ι b₂} {h₁ : ι a₁ = ι b₁} {i₁ : ι a₂ = ι b₂}
    {f₂ : ι a₂ = ι a₃} {g₂ : ι b₂ = ι b₃} {i₂ : ι a₃ = ι b₃}
    (v : ap ι' i₁ ⬝ ap ι' g₂ = ap ι' f₂ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
    ap ι' h₁ ⬝ ap ι' (g₁ ⬝ g₂) = ap ι' (f₁ ⬝ f₂) ⬝ ap ι' i₂ :=
  ((ap_con ι' g₁ g₂)⁻¹) ▹ ((ap_con ι' f₁ f₂)⁻¹) ▹
  @fund_dbl_precat_flat_comp₂ X A C Xtrunc Atrunc Cset
    (ι' (ι a₁)) (ι' (ι a₂)) (ι' (ι a₃)) (ι' (ι b₁)) (ι' (ι b₂)) (ι' (ι b₃))
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
    (ap ι' f₂) (ap ι' g₂) (ap ι' i₂) v u

  --DEFINITIONS FOR THE HORIZONTAL WORM PRECATEGORY
  context
  parameters (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    (ι' : A → X) (ι : C → A)
    {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : C}
    {f₁ : ι a₁ = ι a₂} {g₁ : ι b₁ = ι b₂} {h₁ : ι a₁ = ι b₁} {i₁ : ι a₂ = ι b₂}
    {f₂ : ι a₂ = ι a₃} {g₂ : ι b₂ = ι b₃} {i₂ : ι a₃ = ι b₃}
    {f₃ : ι a₃ = ι a₄} {g₃ : ι b₃ = ι b₄} {i₃ : ι a₄ = ι b₄}
    (w : ap ι' i₂ ⬝ ap ι' g₃ = ap ι' f₃ ⬝ ap ι' i₃)
    (v : ap ι' i₁ ⬝ ap ι' g₂ = ap ι' f₂ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁)
  include Xtrunc Atrunc Cset

  definition fund_dbl_precat_flat_transp5
    (vu : ap ι' h₁ ⬝ (ap ι' g₁ ⬝ ap ι' g₂) = ap ι' (f₁ ⬝ f₂) ⬝ ap ι' i₂) :
  fund_dbl_precat_flat_comp₂ w
    (transport (λ a_1, ap ι' h₁ ⬝ a_1 = ap ι' (f₁ ⬝ f₂) ⬝ ap ι' i₂)
    ((ap_con ι' g₁ g₂)⁻¹) vu)
  = transport (λ a_1, _) ((ap_con ι' g₁ g₂)⁻¹) (fund_dbl_precat_flat_comp₂ w vu) :=
  begin
    apply (eq.rec_on ((ap_con ι' g₁ g₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp6
    (vu : ap ι' h₁ ⬝ (ap ι' g₁ ⬝ ap ι' g₂) = (ap ι' f₁ ⬝ ap ι' f₂) ⬝ ap ι' i₂) :
  fund_dbl_precat_flat_comp₂ w (transport (λ x, _ = x ⬝ _) ((ap_con ι' f₁ f₂)⁻¹) vu)
  = transport (λ x, _) ((ap_con ι' f₁ f₂)⁻¹) (fund_dbl_precat_flat_comp₂ w vu) :=
  begin
    apply (eq.rec_on ((ap_con ι' f₁ f₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp7
    (wv : ap ι' i₁ ⬝ (ap ι' g₂ ⬝ ap ι' g₃) = ap ι' (f₂ ⬝ f₃) ⬝ ap ι' i₃) :
  fund_dbl_precat_flat_comp₂ (transport (λ x, _ ⬝ x = _) ((ap_con ι' g₂ g₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_con ι' g₂ g₃)⁻¹) (fund_dbl_precat_flat_comp₂ wv u) :=
  begin
    apply (eq.rec_on ((ap_con ι' g₂ g₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp8
    (wv : ap ι' i₁ ⬝ (ap ι' g₂ ⬝ ap ι' g₃) = (ap ι' f₂ ⬝ ap ι' f₃) ⬝ ap ι' i₃) :
  fund_dbl_precat_flat_comp₂ (transport (λ x, _ = x ⬝ _) ((ap_con ι' f₂ f₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_con ι' f₂ f₃)⁻¹) (fund_dbl_precat_flat_comp₂ wv u) :=
  begin
    apply (eq.rec_on ((ap_con ι' f₂ f₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_assoc₂_aux {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : A}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    {f₃ : a₃ = a₄} {g₃ : b₃ = b₄} {i₃ : a₄ = b₄}
    (w : (ap ι' i₂) ⬝ (ap ι' g₃) = (ap ι' f₃) ⬝ (ap ι' i₃))
    (v : (ap ι' i₁) ⬝ (ap ι' g₂) = (ap ι' f₂) ⬝ (ap ι' i₂))
    (u : (ap ι' h₁) ⬝ (ap ι' g₁) = (ap ι' f₁) ⬝ (ap ι' i₁)) :
    (transport (λ a_6, _ = (((ap ι' f₁) ⬝ a_6) ⬝ (ap ι' i₃))) (ap_con ι' f₂ f₃)
     (transport (λ a_6, (ap ι' h₁) ⬝ ((ap ι' g₁) ⬝ a_6) = _) (ap_con ι' g₂ g₃)
      (transport (λ a_6, _ = a_6 ⬝ (ap ι' i₃)) (ap_con ι' f₁ (f₂ ⬝ f₃))
       (transport (λ a_6, (ap ι' h₁) ⬝ a_6 = _) (ap_con ι' g₁ (g₂ ⬝ g₃))
        (transport (λ a_6, (ap ι' h₁) ⬝ (ap ι' a_6) = _) (con.assoc g₁ g₂ g₃)
         (transport (λ a_6, _ = (ap ι' a_6) ⬝ (ap ι' i₃)) (con.assoc f₁ f₂ f₃)
          (transport (λ a_6, (ap ι' h₁) ⬝ a_6 = _) ((ap_con ι' (concat g₁ g₂) g₃)⁻¹)
           (transport (λ a_6, _ = a_6 ⬝ (ap ι' i₃)) ((ap_con ι' (concat f₁ f₂) f₃)⁻¹)
            (transport (λ a_6, (ap ι' h₁) ⬝ (a_6 ⬝ (ap ι' g₃)) = _) ((ap_con ι' g₁ g₂)⁻¹)
             (transport (λ a_6, _ = (a_6 ⬝ (ap ι' f₃)) ⬝ (ap ι' i₃)) ((ap_con ι' f₁ f₂)⁻¹)
              (transport (λ a_1, _ = a_1 ⬝ (ap ι' i₃))
                ((con.assoc (ap ι' f₁) (ap ι' f₂) (ap ι' f₃))⁻¹)
                (transport (λ a_0, (ap ι' h₁) ⬝ a_0 = _)
                  ((con.assoc (ap ι' g₁) (ap ι' g₂) (ap ι' g₃))⁻¹)
                  (fund_dbl_precat_flat_comp₂
                    (fund_dbl_precat_flat_comp₂ w v) u)))))))))))))
    = (fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_comp₂ w v) u) :=
  begin
    reverts [u, v, w],
    revert i₃, revert g₃, revert f₃,
    revert i₂, revert g₂, revert f₂,
    revert i₁, revert g₁, revert f₁,
    intro f₁, cases f₁,
    intro g₁, cases g₁,
    intro i₁,
    intro f₂, cases f₂,
    intro g₂, cases g₂,
    intro i₂,
    intro f₃, cases f₃,
    intro g₃, cases g₃,
    intros, apply idp,
  end

  definition fund_dbl_precat_assoc₂ :
    (con.assoc g₁ g₂ g₃) ▹ (con.assoc f₁ f₂ f₃) ▹
      (fund_dbl_precat_comp₂ w (fund_dbl_precat_comp₂ v u))
    = (fund_dbl_precat_comp₂ (fund_dbl_precat_comp₂ w v) u) :=
  begin
    unfold fund_dbl_precat_comp₂,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp5, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp6, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_assoc₂',
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply inverse,
    apply concat, apply fund_dbl_precat_flat_transp7, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_transp8, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_assoc₂_aux,
  end

  definition fund_dbl_precat_id₂ [reducible] {a b : C} (f : ι a = ι b) :
    ap ι' f ⬝ ap ι' (refl (ι b)) = ap ι' (refl (ι a)) ⬝ ap ι' f :=
  (idp_con (ap ι' f))⁻¹

  definition fund_dbl_precat_id₂_left_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝ (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, _ = a_6 ⬝ (ap ι' i)) (ap_con ι' f (refl b))
      (transport (λ a_6, (ap ι' h) ⬝ a_6 = _) (ap_con ι' g (refl d))
        (transport (λ a_6, _ = (ap ι' a_6) ⬝ (ap ι' i)) ((con_idp f)⁻¹)
          (transport (λ a_6, (ap ι' h) ⬝ (ap ι' a_6) = _) ((con_idp g)⁻¹) u))))
    = u :=
  begin
    revert u, revert i,
    cases g,
    cases f,
    intros, apply idp,
  end

  definition fund_dbl_precat_id₂_left (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    transport (λ x, (ap ι' h) ⬝ (ap ι' x) = _) (con_idp g)
     (transport (λ x, _ = (ap ι' x) ⬝ _) (con_idp f)
       (fund_dbl_precat_comp₂ (fund_dbl_precat_id₂ i) u)) = u :=
  begin
    unfold fund_dbl_precat_comp₂,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_id₂_left,
    apply inverse, apply fund_dbl_precat_id₂_left_aux,
  end

  definition fund_dbl_precat_id₂_right_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, (ap ι' h) ⬝ a_6 = _) (idp_con (ap ι' g))
      (transport (λ a_6, _ =  a_6 ⬝ (ap ι' i)) (idp_con (ap ι' f))
        (transport (λ a_6, _ = a_6 ⬝ (ap ι' i)) (ap_con ι' (refl a) f)
          (transport (λ a_6, (ap ι' h) ⬝ a_6 = _) (ap_con ι' (refl c) g)
            (transport (λ a_6, _ = (ap ι' a_6) ⬝ (ap ι' i)) ((idp_con f)⁻¹)
              (transport (λ a_6, (ap ι' h) ⬝ (ap ι' a_6) = _) ((idp_con g)⁻¹) u))))))
    = u :=
  begin
    revert u,
    revert i, revert f, revert g,
    intro g, cases g,
    intro f, cases f,
    intros, apply idp,
  end

  definition fund_dbl_precat_id₂_right  (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ x, (ap ι' h) ⬝ (ap ι' x) = _) (idp_con g)
      (transport (λ x, _ = (ap ι' x) ⬝ _) (idp_con f)
        (fund_dbl_precat_comp₂ u (fund_dbl_precat_id₂ h))))
    = u :=
  begin
    unfold fund_dbl_precat_comp₂,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_id₂_right',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_id₂_right_aux,
  end

  definition fund_dbl_precat_left_inverse₁_aux1 {a b c d : A}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    fund_dbl_precat_flat_comp₁
      (transport (λ x, _ = _ ⬝ x) (inverse (ap_inv ι' i))
        (transport (λ x, x ⬝ _ = _) (inverse (ap_inv ι' h))
             (fund_dbl_precat_flat_inv₁ u)))
      u
    = (inverse (ap_inv ι' i)) ▹ (inverse (ap_inv ι' h)) ▹
      fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_inv₁ u) u :=
  begin
    cases i, cases h, apply idp,
  end

  definition fund_dbl_precat_left_inverse₁_aux2 {a b c d : A}
    {f : a = b} {h : a = c} {i : b = d} :
    (transport (λ x, _ = _ ⬝ x) (con.right_inv (ap ι' i))
     (transport (λ x, x ⬝ _ = _) (con.right_inv (ap ι' h))
      (transport (λ x, (_ ⬝ x) ⬝ _ = _) (ap_inv ι' h)
       (transport (λ x, _ = _ ⬝ (_ ⬝ x)) (ap_inv ι' i)
        (transport (λ x, x ⬝ _ = _) (ap_con ι' h (inverse h))
         (transport (λ x, _ = _ ⬝ x) (ap_con ι' i (inverse i))
          (transport (λ x, (ap ι' x) ⬝ _ = _) (inverse (con.right_inv h))
           (transport (λ x, (ap ι' idp) ⬝ (ap ι' f) = (ap ι' f) ⬝ (ap ι' x))
             (inverse (con.right_inv i))
             (idp_con (ap ι' f))))))))))
    = idp_con (ap ι' f) :=
  begin
    cases f, cases h, cases i, apply idp,
  end

  definition fund_dbl_precat_left_inverse₁ {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    transport (λ x, _ = ap ι' f ⬝ ap ι' x) (con.right_inv i)
      (transport (λ x, ap ι' x ⬝ ap ι' f = _) (con.right_inv h)
        (fund_dbl_precat_comp₁ (fund_dbl_precat_inv₁ u) u))
    = fund_dbl_precat_id₁ X A C ι' ι f :=
  begin
    unfold fund_dbl_precat_comp₁, unfold fund_dbl_precat_id₁, unfold fund_dbl_precat_inv₁,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_left_inverse₁_aux1,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_left_inverse₁',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_left_inverse₁_aux2,
  end

  definition fund_dbl_precat_right_inverse₁_aux1 {a b c d : A}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    fund_dbl_precat_flat_comp₁ u
      (transport (λ x, _ = _ ⬝ x) (inverse (ap_inv ι' i))
        (transport (λ x, x ⬝ _ = _) (inverse (ap_inv ι' h))
          (fund_dbl_precat_flat_inv₁ u)))
    = (inverse (ap_inv ι' i)) ▹ (inverse (ap_inv ι' h)) ▹
      fund_dbl_precat_flat_comp₁ u (fund_dbl_precat_flat_inv₁ u) :=
  begin
    cases i, cases h, apply idp,
  end

  definition fund_dbl_precat_right_inverse₁_aux2 {a b c d : A}
    {g : c = d} {h : a = c} {i : b = d} :
    transport (λ x, _ = _ ⬝ x) (con.left_inv (ap ι' i))
     (transport (λ x, x ⬝ _ = _) (con.left_inv (ap ι' h))
      (transport (λ x, (x ⬝ _) ⬝ _ = _) (ap_inv ι' h)
       (transport (λ x, _ = _ ⬝ (x ⬝ _)) (ap_inv ι' i)
        (transport (λ x, x ⬝ _ = _) (ap_con ι' (inverse h) h)
         (transport (λ x, _ = _ ⬝ x) (ap_con ι' (inverse i) i)
          (transport (λ x, (ap ι' x) ⬝ _ = _) (inverse (con.left_inv h))
            (transport (λ x, ap ι' idp ⬝ ap ι' g = ap ι' g ⬝ ap ι' x)
              (inverse (con.left_inv i))
              (idp_con (ap ι' g)))))))))
    = idp_con (ap ι' g) :=
  begin
    cases g, cases h, cases i, apply idp,
  end

  definition fund_dbl_precat_right_inverse₁ {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    transport (λ x, _ = _ ⬝ (ap ι' x)) (con.left_inv i)
      (transport (λ x, (ap ι' x) ⬝ _ = _) (con.left_inv h)
        (fund_dbl_precat_comp₁ u (fund_dbl_precat_inv₁ u)))
    = fund_dbl_precat_id₁ X A C ι' ι g :=
  begin
    unfold fund_dbl_precat_comp₁, unfold fund_dbl_precat_id₁, unfold fund_dbl_precat_inv₁,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_right_inverse₁_aux1,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_right_inverse₁',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse,  apply fund_dbl_precat_right_inverse₁_aux2,
  end

  definition fund_dbl_precat_left_inverse₂_aux1 {a b c d : A}
    {f : a = b} {g : c = d} {h : a = c} {i: b = d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    fund_dbl_precat_flat_comp₂
      (transport (λ x, _ ⬝ x = _) (inverse (ap_inv ι' g))
        (transport (λ x, _ = x ⬝ _) (inverse (ap_inv ι' f))
             (fund_dbl_precat_flat_inv₂ u)))
      u
    = (inverse (ap_inv ι' g)) ▹ (inverse (ap_inv ι' f)) ▹
      fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_inv₂ u) u :=
  begin
    cases f, cases g, apply idp,
  end

  definition fund_dbl_precat_left_inverse₂_aux2 {a b c d : A}
    {f : a = b} {g : c = d} {h : a = c} :
    transport (λ x, _ ⬝ x = _) (con.right_inv (ap ι' g))
     (transport (λ x, _ = x ⬝ _) (con.right_inv (ap ι' f))
      (transport (λ x, _ = (_ ⬝ x) ⬝ _) (ap_inv ι' f)
       (transport (λ x, _ ⬝ (_ ⬝ x) = _) (ap_inv ι' g)
        (transport (λ x, _ = x ⬝ _) (ap_con ι' f (inverse f))
         (transport (λ x, _ ⬝ x = _) (ap_con ι' g (inverse g))
          (transport (λ x, _ = ap ι' x ⬝ _) (inverse (con.right_inv f))
           (transport (λ x, ap ι' h ⬝ ap ι' x = ap ι' idp ⬝ ap ι' h)
             (inverse (con.right_inv g))
             (inverse (idp_con (ap ι' h))))))))))
     = inverse (idp_con (ap ι' h)) :=
  begin
    cases h, cases f, cases g,
    apply idp,
  end

  definition fund_dbl_precat_left_inverse₂ {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    transport (λ x, _ ⬝ (ap ι' x) = _) (con.right_inv g)
      (transport (λ x, _ = (ap ι' x) ⬝  _) (con.right_inv f)
        (fund_dbl_precat_comp₂ (fund_dbl_precat_inv₂ u) u))
    = fund_dbl_precat_id₂ h :=
  begin
    unfold fund_dbl_precat_comp₂, unfold fund_dbl_precat_inv₂,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_left_inverse₂_aux1,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_left_inverse₂',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_left_inverse₂_aux2,
  end

  definition fund_dbl_precat_right_inverse₂_aux1 {a b c d : A}
    {f : a = b} {g : c = d} {h : a = c} {i: b = d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    fund_dbl_precat_flat_comp₂ u
      (transport (λ x, _ ⬝ x = _) (ap_inv ι' g)⁻¹
        (transport (λ x, _ = x ⬝ _) (ap_inv ι' f)⁻¹
          (fund_dbl_precat_flat_inv₂ u)))
    = (ap_inv ι' g)⁻¹ ▹ (ap_inv ι' f)⁻¹ ▹
    fund_dbl_precat_flat_comp₂ u (fund_dbl_precat_flat_inv₂ u) :=
  begin
    cases g, cases f, apply idp,
  end

  definition fund_dbl_precat_right_inverse₂_aux2  {a b c d : A}
    {f : a = b} {g : c = d} {i: b = d} :
    transport (λ x, _ ⬝ x = _) (con.left_inv (ap ι' g))
     (transport (λ x, _ = x ⬝ _) (con.left_inv (ap ι' f))
      (transport (λ x, _ = (x ⬝ _) ⬝ _) (ap_inv ι' f)
       (transport (λ x, _ ⬝ (x ⬝ _) = _) (ap_inv ι' g)
        (transport (λ x, _ = x ⬝ _) (ap_con ι' (inverse f) f)
         (transport (λ x, _ ⬝ x = _) (ap_con ι' (inverse g) g)
          (transport (λ x, _ = ap ι' x ⬝ _) (inverse (con.left_inv f))
           (transport (λ x, ap ι' i ⬝ ap ι' x = ap ι' idp ⬝ ap ι' i)
             (inverse (con.left_inv g))
             (idp_con (ap ι' i))⁻¹)))))))
    = (idp_con (ap ι' i))⁻¹ :=
  begin
    cases i, cases f, cases g, apply idp,
  end

  definition fund_dbl_precat_right_inverse₂ {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (u : ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :
    transport (λ x, _ ⬝ ap ι' x = _) (con.left_inv g)
      (transport (λ x, _ = ap ι' x ⬝ _) (con.left_inv f)
        (fund_dbl_precat_comp₂ u (fund_dbl_precat_inv₂ u)))
    = fund_dbl_precat_id₂ i :=
  begin
    unfold fund_dbl_precat_comp₂, unfold fund_dbl_precat_inv₂,
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_right_inverse₂_aux1,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_flat_right_inverse₂',
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_right_inverse₂_aux2,
  end

  end

  context
  parameters (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    (ι' : A → X) (ι : C → A)
  include Xtrunc Atrunc Cset

  definition fund_dbl_precat_id_comp₁_aux (a b c : A)
    (f : a = b) (g : b = c) :
    fund_dbl_precat_flat_comp₁ (inverse (idp_con (ap ι' g)))
       (inverse (idp_con (ap ι' f)))
    = transport (λ a_6, a_6 ⬝ (ap ι' (refl c)) = _) (ap_con ι' f g)
       (transport (λ a_6, _ = (ap ι' (refl a)) ⬝ a_6) (ap_con ι' f g)
          (inverse (idp_con (ap ι' (concat f g))))) :=
  begin
    revert g, cases f,
    intro g, cases g,
    apply idp,
  end

  definition fund_dbl_precat_id_comp₁ (a b c : C)
    (f : ι a = ι b) (g : ι b = ι c) :
    fund_dbl_precat_id₂ X A C ι' ι (f ⬝ g)
    = fund_dbl_precat_comp₁ (fund_dbl_precat_id₂ X A C ι' ι g)
      (fund_dbl_precat_id₂ X A C ι' ι f) :=
  begin
    apply inverse,
    unfold fund_dbl_precat_comp₁, unfold fund_dbl_precat_id₂,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply fund_dbl_precat_id_comp₁_aux,
  end

  definition fund_dbl_precat_id_comp₂_aux (a b c : A)
    (f : a = b) (g : b = c) :
    fund_dbl_precat_flat_comp₂ (idp_con (ap ι' g)) (idp_con (ap ι' f))
    = transport (λ x, _ = x ⬝ _) (ap_con ι' f g)
       (transport (λ x, _ ⬝ x = _) (ap_con ι' f g)
          (idp_con (ap ι' (concat f g)))) :=
  begin
    revert g, cases f,
    intro g, cases g,
    apply idp,
  end

  definition fund_dbl_precat_id_comp₂ (a b c : C)
    (f : ι a = ι b) (g : ι b = ι c) :
    fund_dbl_precat_id₁ X A C ι' ι (f ⬝ g)
    = fund_dbl_precat_comp₂ (fund_dbl_precat_id₁ X A C ι' ι g)
      (fund_dbl_precat_id₁ X A C ι' ι f) :=
  begin
    apply inverse,
    unfold fund_dbl_precat_comp₂, unfold fund_dbl_precat_id₁,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply fund_dbl_precat_id_comp₂_aux,
  end

  definition fund_dbl_precat_thin {a b c d : C}
    {f : ι a = ι b} {g : ι c = ι d} {h : ι a = ι c} {i : ι b = ι d}
    (comm : h ⬝ g = f ⬝ i) :
    ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i :=
  calc ap ι' h ⬝ ap ι' g = ap ι' (h ⬝ g) : ap_con
                    ... = ap ι' (f ⬝ i) : comm
                    ... = ap ι' f ⬝ ap ι' i : ap_con

  definition fund_dbl_precat_thin_id₁_aux {a b : A} (f : a = b) :
    (ap_con ι' idp f)⁻¹
    ⬝ (transport (λ x, _ = ap ι' x) (idp_con f ⬝ (con_idp f)⁻¹)
       (refl (ap ι' (concat idp f)))) ⬝ (ap_con ι' f idp)
    = idp_con (ap ι' f) :=
  begin
    cases f, apply idp,
  end

  definition fund_dbl_precat_thin_id₁ {a b : C} (f : ι a = ι b) :
    fund_dbl_precat_thin ((idp_con f) ⬝ (con_idp f)⁻¹)
    = fund_dbl_precat_id₁ X A C ι' ι f :=
  begin
    esimp {fund_dbl_precat_thin, fund_dbl_precat_id₁},
    apply fund_dbl_precat_thin_id₁_aux,
  end

  definition fund_dbl_precat_thin_id₂_aux {a b : A} (f : a = b) :
    (ap_con ι' f idp)⁻¹
    ⬝ (transport (λ x, _ = ap ι' x) ((con_idp f) ⬝ (idp_con f)⁻¹)
       (refl (ap ι' (concat f idp)))) ⬝ (ap_con ι' idp f)
    = (idp_con (ap ι' f))⁻¹ :=
  begin
    cases f, apply idp,
  end

  definition fund_dbl_precat_thin_id₂ {a b : C} (f : ι a = ι b) :
    fund_dbl_precat_thin ((con_idp f) ⬝ (idp_con f)⁻¹)
    = fund_dbl_precat_id₂ X A C ι' ι f :=
  begin
    esimp {fund_dbl_precat_thin, fund_dbl_precat_id₂},
    apply fund_dbl_precat_thin_id₂_aux,
  end

  attribute is_trunc_eq [instance]
  definition fund_dbl_precat_thin_comp₁_aux {a b c₁ d₁ c₂ d₂ : A}
    (f₁ : a = b) (g₁ : c₁ = d₁) (h₁ : a = c₁) (i₁ : b = d₁)
    (g₂ : c₂ = d₂) (h₂ : c₁ = c₂) (i₂ : d₁ = d₂)
    (pv : h₂ ⬝ g₂ = g₁ ⬝ i₂) (pu : h₁ ⬝ g₁ = f₁ ⬝ i₁)
    (px : (h₁ ⬝ h₂) ⬝ g₂ = f₁ ⬝ (i₁ ⬝ i₂)) :
    transport (λ x, _ = _ ⬝ x) (inverse (ap_con ι' i₁ i₂))
      (transport (λ x, x ⬝ _ = _) (inverse (ap_con ι' h₁ h₂))
        (fund_dbl_precat_flat_comp₁
          (((ap_con ι' h₂ g₂)⁻¹ ⬝
            (transport (λ x, eq (ap ι' (concat h₂ g₂)) (ap ι' x)) pv
              (refl (ap ι' (concat h₂ g₂))))) ⬝ (ap_con ι' g₁ i₂))
           (((ap_con ι' h₁ g₁)⁻¹ ⬝
             (transport (λ x, _ = ap ι' x) pu (refl (ap ι' (concat h₁ g₁)))))
               ⬝ (ap_con ι' f₁ i₁))))
    = (((ap_con ι' (concat h₁ h₂) g₂)⁻¹
          ⬝ (transport (λ x, eq (ap ι' (concat (concat h₁ h₂) g₂)) (ap ι' x)) px
             (refl (ap ι' (concat (concat h₁ h₂) g₂)))))
       ⬝ (ap_con ι' f₁ (concat i₁ i₂))) :=
  begin
    esimp {fund_dbl_precat_flat_comp₁},
    cases i₂, cases i₁,
    cases h₂, cases h₁,
    cases g₂, cases px, cases pv,
    assert P1 : pu = (refl (refl d₂)),
      apply @is_hset.elim,
    rewrite P1,
  end

  definition fund_dbl_precat_thin_comp₂_aux {a b c₁ d₁ c₂ d₂ : A}
    (f₁ : a = b) (g₁ : c₁ = d₁) (h₁ : a = c₁) (i₁ : b = d₁)
    (g₂ : c₂ = d₂) (h₂ : c₁ = c₂) (i₂ : d₁ = d₂)
    (pv : g₁ ⬝ i₂ = h₂ ⬝ g₂) (pu : f₁ ⬝ i₁ = h₁ ⬝ g₁)
    (px : f₁ ⬝ (i₁ ⬝ i₂) = (h₁ ⬝ h₂) ⬝ g₂) :
    (transport (λ x, _ ⬝ x = _) (inverse (ap_con ι' i₁ i₂))
      (transport (λ x, _ = x ⬝ _) (inverse (ap_con ι' h₁ h₂))
        (fund_dbl_precat_flat_comp₂
          (((ap_con ι' g₁ i₂)⁻¹ ⬝
            (transport (λ x, eq (ap ι' (concat g₁ i₂)) (ap ι' x)) pv
              (refl (ap ι' (concat g₁ i₂))))) ⬝ (ap_con ι' h₂ g₂))
          (((ap_con ι' f₁ i₁)⁻¹ ⬝
             (transport (λ x, eq (ap ι' (concat f₁ i₁)) (ap ι' x)) pu
               (refl (ap ι' (concat f₁ i₁))))) ⬝ (ap_con ι' h₁ g₁)))))
    = (((ap_con ι' f₁ (concat i₁ i₂))⁻¹ ⬝
          (transport (λ x, eq (ap ι' (concat f₁ (concat i₁ i₂))) (ap ι' x)) px
             (refl (ap ι' (concat f₁ (concat i₁ i₂))))))
       ⬝ (ap_con ι' (concat h₁ h₂) g₂)) :=
  begin
    esimp {fund_dbl_precat_flat_comp₂},
    cases i₂, cases i₁,
    cases h₂, cases h₁,
    cases g₂, cases px, cases pv,
    assert P1 : pu = (refl (refl d₂)),
      apply @is_hset.elim,
    rewrite P1,
  end

  set_option pp.notation false
  definition fund_dbl_precat_thin_comp₁ {a b c₁ d₁ c₂ d₂ : C}
    (f₁ : ι a = ι b) (g₁ : ι c₁ = ι d₁) (h₁ : ι  a = ι c₁) (i₁ : ι b = ι d₁)
    (g₂ : ι c₂ = ι d₂) (h₂ : ι c₁ = ι c₂) (i₂ : ι d₁ = ι d₂)
    (pv : h₂ ⬝ g₂ = g₁ ⬝ i₂) (pu : h₁ ⬝ g₁ = f₁ ⬝ i₁)
    (px : (h₁ ⬝ h₂) ⬝ g₂ = f₁ ⬝ (i₁ ⬝ i₂)) :
    fund_dbl_precat_comp₁ (fund_dbl_precat_thin pv) (fund_dbl_precat_thin pu)
    = fund_dbl_precat_thin px :=
  begin
    esimp {fund_dbl_precat_thin, fund_dbl_precat_comp₁},
    apply fund_dbl_precat_thin_comp₁_aux,
  end

  definition fund_dbl_precat_thin_comp₂ {a b c₁ d₁ c₂ d₂ : C}
    (f₁ : ι a = ι b) (g₁ : ι c₁ = ι d₁) (h₁ : ι a = ι c₁) (i₁ : ι b = ι d₁)
    (g₂ : ι c₂ = ι d₂) (h₂ : ι c₁ = ι c₂) (i₂ : ι d₁ = ι d₂)
    (pv : g₁ ⬝ i₂ = h₂ ⬝ g₂) (pu : f₁ ⬝ i₁ = h₁ ⬝ g₁)
    (px : f₁ ⬝ (i₁ ⬝ i₂) = (h₁ ⬝ h₂) ⬝ g₂) :
    fund_dbl_precat_comp₂ (fund_dbl_precat_thin pv) (fund_dbl_precat_thin pu)
    = fund_dbl_precat_thin px :=
  begin
    esimp {fund_dbl_precat_thin, fund_dbl_precat_comp₂},
    apply fund_dbl_precat_thin_comp₂_aux,
  end

  variables {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : C}
    {f₀₀ : ι a₀₀ = ι a₀₁} {f₀₁ : ι a₀₁ = ι a₀₂}
    {f₁₀ : ι a₁₀ = ι a₁₁} {f₁₁ : ι a₁₁ = ι a₁₂}
    {f₂₀ : ι a₂₀ = ι a₂₁} {f₂₁ : ι a₂₁ = ι a₂₂}
    {g₀₀ : ι a₀₀ = ι a₁₀} {g₀₁ : ι a₀₁ = ι a₁₁}
    {g₀₂ : ι a₀₂ = ι a₁₂} {g₁₀ : ι a₁₀ = ι a₂₀}
    {g₁₁ : ι a₁₁ = ι a₂₁} {g₁₂ : ι a₁₂ = ι a₂₂}
    (x : ap ι' g₁₁ ⬝ ap ι' f₂₁ = ap ι' f₁₁ ⬝ ap ι' g₁₂)
    (w : ap ι' g₁₀ ⬝ ap ι' f₂₀ = ap ι' f₁₀ ⬝ ap ι' g₁₁)
    (v : ap ι' g₀₁ ⬝ ap ι' f₁₁ = ap ι' f₀₁ ⬝ ap ι' g₀₂)
    (u : ap ι' g₀₀ ⬝ ap ι' f₁₀ = ap ι' f₀₀ ⬝ ap ι' g₀₁)

  definition fund_dbl_precat_interchange :
    fund_dbl_precat_comp₁ (fund_dbl_precat_comp₂ x w)
      (fund_dbl_precat_comp₂ v u) = fund_dbl_precat_comp₂ (fund_dbl_precat_comp₁ x v)
      (fund_dbl_precat_comp₁ w u) :=
  begin
    unfold fund_dbl_precat_comp₂, unfold fund_dbl_precat_comp₁,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply fund_dbl_precat_interchange_aux,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply concat, apply inverse, apply fund_dbl_precat_flat_interchange,
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_tr_of_inv_tr_eq, apply eq_tr_of_inv_tr_eq,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply inverse, apply concat, apply fund_dbl_precat_interchange_aux2,
    apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
    apply inverse, apply fund_dbl_precat_interchange_aux3,
  end

  definition fundamental_dbl_precat : dbl_gpd (fundamental_groupoid)
    (λ (a b c d : C) (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d),
      ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :=
  begin
    fapply dbl_gpd.mk,
      intros, apply (fund_dbl_precat_comp₁ a_1 a_2),
      intros, apply (@fund_dbl_precat_id₁ X A C Xtrunc Atrunc Cset ι' ι a b f),
      intros, apply fund_dbl_precat_assoc₁,
      intros, apply fund_dbl_precat_id₁_left,
      intros, apply fund_dbl_precat_id₁_right,
      intros, apply is_trunc_eq, apply is_trunc_eq, apply Xtrunc,
      intros, apply (fund_dbl_precat_comp₂ a_1 a_2),
      intros, apply (@fund_dbl_precat_id₂ X A C Xtrunc Atrunc Cset ι' ι a b f),
      intros, apply fund_dbl_precat_assoc₂,
      intros, apply fund_dbl_precat_id₂_left,
      intros, apply fund_dbl_precat_id₂_right,
      intros, apply is_trunc_eq, apply is_trunc_eq, apply Xtrunc,
      intros, apply fund_dbl_precat_id_comp₁,
      intros, apply fund_dbl_precat_id_comp₂,
      intros, apply idp,
      intros, apply fund_dbl_precat_interchange,
      intros, apply (fund_dbl_precat_inv₁ a_1),
      intros, apply fund_dbl_precat_left_inverse₁,
      intros, apply fund_dbl_precat_right_inverse₁,
      intros, apply (fund_dbl_precat_inv₂ a_1),
      intros, apply fund_dbl_precat_left_inverse₂,
      intros, apply fund_dbl_precat_right_inverse₂,
      intros, apply (fund_dbl_precat_thin a_1),
    fapply thin_structure.mk,
      intros, apply fund_dbl_precat_thin_id₁,
      intros, apply fund_dbl_precat_thin_id₂,
      intros, apply fund_dbl_precat_thin_comp₁,
      intros, apply fund_dbl_precat_thin_comp₂,
  end

  end
end dbl_gpd
