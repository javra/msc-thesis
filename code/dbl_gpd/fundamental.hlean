import algebra.groupoid ..transport4
import .decl

open dbl_precat precategory truncation eq nat groupoid morphism sigma sigma.ops

namespace dbl_gpd
  variables {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
  include Xtrunc Atrunc Cset

  set_option pp.beta true
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
    (λ (a b : C), have ish : is_hset (ι a = ι b), from succ_is_trunc nat.zero (ι a) (ι b), ish)
    (λ (a b c : C) (p : ι b = ι c) (q : ι a = ι b), q ⬝ p)
    (λ (a : C), refl (ι a))
    (λ (a b c d : C) (p : ι c = ι d) (q : ι b = ι c) (r : ι a = ι b), concat_pp_p r q p)
    (λ (a b : C) (p : ι a = ι b), concat_p1 p)
    (λ (a b : C) (p : ι a = ι b), concat_1p p)
    (λ ⦃a b : C⦄ (p : ι a = ι b), @is_iso.mk C _ a b p (p⁻¹) !concat_pV !concat_Vp)

  --FLAT VERSIONS
  definition fund_dbl_precat_flat_comp₁ {a₁ b₁ a₂ b₂ a₃ b₃ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    (h₁ ⬝ h₂) ⬝ g₂ = f₁ ⬝ (i₁ ⬝ i₂) :=
  calc (h₁ ⬝ h₂) ⬝ g₂ = h₁ ⬝ (h₂ ⬝ g₂) : concat_pp_p
                 ... = h₁ ⬝ (g₁ ⬝ i₂) : v
                 ... = (h₁ ⬝ g₁) ⬝ i₂ : concat_p_pp
                 ... = (f₁ ⬝ i₁) ⬝ i₂ : u
                 ... = f₁ ⬝ (i₁ ⬝ i₂) : concat_pp_p

  definition fund_dbl_precat_flat_comp₂ {a₁ a₂ a₃ b₁ b₂ b₃ : X}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    (v : i₁ ⬝ g₂ = f₂ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    h₁ ⬝ (g₁ ⬝ g₂) = (f₁ ⬝ f₂) ⬝ i₂ :=
  calc h₁ ⬝ (g₁ ⬝ g₂) = (h₁ ⬝ g₁) ⬝ g₂ : concat_p_pp
                 ... = (f₁ ⬝ i₁) ⬝ g₂ : u
                 ... = f₁ ⬝ (i₁ ⬝ g₂) : concat_pp_p
                 ... = f₁ ⬝ (f₂ ⬝ i₂) : v
                 ... = (f₁ ⬝ f₂) ⬝ i₂ : concat_p_pp

  definition fund_dbl_precat_flat_assoc₁ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    {g₃ : a₄ = b₄} {h₃ : a₃ = a₄} {i₃ : b₃ = b₄}
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    concat_pp_p i₁ i₂ i₃ ▹ concat_pp_p h₁ h₂ h₃ ▹
      (fund_dbl_precat_flat_comp₁ w (fund_dbl_precat_flat_comp₁ v u))
    = fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₁ w v) u :=
  begin
    revert u, revert f₁, revert h₁, revert i₁,
    revert v, revert g₁, revert h₂, revert i₂,
    revert w, revert g₂, revert h₃, revert g₃, apply (eq.rec_on i₃),
    intro g₃, apply (eq.rec_on g₃),
    intros (h₃, g₂, w), apply (eq.rec_on w),
    apply (eq.rec_on h₃),
    intro i₂, apply (eq.rec_on i₂),
    intros (h₂, g₁, v), apply (eq.rec_on v),
    apply (eq.rec_on h₂),
    intro i₁, apply (eq.rec_on i₁),
    intros (h₁, g₁, u), apply (eq.rec_on u),
    apply (eq.rec_on h₁),
    apply idp,
  end

  definition fund_dbl_precat_flat_assoc₂ {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : X}
    {f₁ : a₁ = a₂} {g₁ : b₁ = b₂} {h₁ : a₁ = b₁} {i₁ : a₂ = b₂}
    {f₂ : a₂ = a₃} {g₂ : b₂ = b₃} {i₂ : a₃ = b₃}
    {f₃ : a₃ = a₄} {g₃ : b₃ = b₄} {i₃ : a₄ = b₄}
    (w : i₂ ⬝ g₃ = f₃ ⬝ i₃)
    (v : i₁ ⬝ g₂ = f₂ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
    concat_pp_p g₁ g₂ g₃ ▹ concat_pp_p f₁ f₂ f₃ ▹
      (fund_dbl_precat_flat_comp₂ w (fund_dbl_precat_flat_comp₂ v u))
    = fund_dbl_precat_flat_comp₂ (fund_dbl_precat_flat_comp₂ w v) u :=
  begin
    revert v,
    revert w, revert f₃, revert f₂, revert i₃, revert i₂,
    revert u, revert h₁, revert i₁,
    revert g₃, revert g₂, revert g₁,
    intro g₁, apply (eq.rec_on g₁),
    intro g₂, apply (eq.rec_on g₂),
    intro g₃, apply (eq.rec_on g₃),
    intro i₁, apply (eq.rec_on i₁),
    intro h₁, intro u, apply (eq.rec_on u),
    apply (eq.rec_on h₁),
    intro i₂, apply (eq.rec_on i₂),
    intro i₃, apply (eq.rec_on i₃),
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
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (fund_dbl_precat_flat_assoc₁ w v u))

  definition fund_dbl_precat_flat_id₁ {a b : X} (g : a = b) :
    refl a ⬝ g = g ⬝ refl b :=
  concat_1p g

  definition fund_dbl_precat_flat_id₂ {a b : X} (g : a = b) :
    g ⬝ refl b = refl a ⬝ g :=
  (concat_1p g)⁻¹

  definition fund_dbl_precat_flat_id₁_left {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_id₁ g) u = u :=
  begin
    revert u, revert f, revert h, revert i,
    apply (eq.rec_on g),
    intro i, apply (eq.rec_on i),
    intros, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_id₁_right {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    transport (λ x, _ = _ ⬝ x) (!concat_1p)
      (transport (λ x, x ⬝ _ = _) (!concat_1p)
        (fund_dbl_precat_flat_comp₁ u (fund_dbl_precat_flat_id₁ f)))
    = u :=
  begin
    revert u, revert f, revert h, revert i,
    apply (eq.rec_on g),
    intro i, apply (eq.rec_on i),
    intro h, apply (eq.rec_on h),
    intros, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_id₁_right'  {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (fund_dbl_precat_flat_id₁_right u))


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
  ((ap_pp ι' i₁ i₂)⁻¹) ▹ ((ap_pp ι' h₁ h₂)⁻¹)
  ▹ @fund_dbl_precat_flat_comp₁ X A C Xtrunc Atrunc Cset
    (ι' (ι a₁)) (ι' (ι b₁)) (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₃)) (ι' (ι b₃))
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
    (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) v u

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
    ((ap_pp ι' i₁ i₂)⁻¹) vu)
  = transport (λ a_1, _) ((ap_pp ι' i₁ i₂)⁻¹) (fund_dbl_precat_flat_comp₁ w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' i₁ i₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp2
    (vu : ap ι' h₁ ⬝ ap ι' h₂ ⬝ ap ι' g₂ = ap ι' f₁ ⬝ (ap ι' i₁ ⬝ ap ι' i₂)) :
  fund_dbl_precat_flat_comp₁ w (transport (λ x, x ⬝ _ = _) ((ap_pp ι' h₁ h₂)⁻¹) vu)
  = transport (λ x, _) ((ap_pp ι' h₁ h₂)⁻¹) (fund_dbl_precat_flat_comp₁ w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' h₁ h₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp3
    (wv : ap ι' (h₂ ⬝ h₃) ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, _ = _ ⬝ x) ((ap_pp ι' i₂ i₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' i₂ i₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' i₂ i₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp4
    (wv : ap ι' h₂ ⬝ ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, x ⬝ _ = _) ((ap_pp ι' h₂ h₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' h₂ h₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' h₂ h₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_assoc₁_aux {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : A}
    (f₁ : a₁ = b₁) (g₁ : a₂ = b₂) (h₁ : a₁ = a₂) (i₁ : b₁ = b₂)
    (g₂ : a₃ = b₃) (h₂ : a₂ = a₃) (i₂ : b₂ = b₃) (g₃ : a₄ = b₄)
    (h₃ : a₃ = a₄) (i₃ : b₃ = b₄)
    (w : (ap ι' h₃) ⬝ (ap ι' g₃) = (ap ι' g₂) ⬝ (ap ι' i₃))
    (v : (ap ι' h₂) ⬝ (ap ι' g₂) = (ap ι' g₁) ⬝ (ap ι' i₂))
    (u : (ap ι' h₁) ⬝ (ap ι' g₁) = (ap ι' f₁) ⬝ (ap ι' i₁)) :
    (transport (λ a_6, ((ap ι' h₁) ⬝ a_6) ⬝ (ap ι' g₃) = _) (ap_pp ι' h₂ h₃)
      (transport (λ a_6, _ =  ((ap ι' f₁) ⬝ ((ap ι' i₁) ⬝ a_6))) (ap_pp ι' i₂ i₃)
        (transport (λ a_6, (a_6 ⬝ (ap ι' g₃)) = _) (ap_pp ι' h₁ (concat h₂ h₃))
          (transport (λ a_6, _ = (ap ι' f₁) ⬝ a_6) (ap_pp ι' i₁ (concat i₂ i₃))
            (transport (λ a_6, _ = (ap ι' f₁) ⬝ (ap ι' a_6)) (concat_pp_p i₁ i₂ i₃)
              (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g₃) = _) (concat_pp_p h₁ h₂ h₃)
                (transport (λ a_6, _ =  (ap ι' f₁) ⬝ a_6) ((ap_pp ι' (concat i₁ i₂) i₃)⁻¹)
                  (transport (λ a_6, a_6 ⬝ (ap ι' g₃) = _) ((ap_pp ι' (concat h₁ h₂) h₃)⁻¹)
                    (transport (λ a_6, _ = (ap ι' f₁) ⬝ (a_6 ⬝ (ap ι' i₃))) ((ap_pp ι' i₁ i₂)⁻¹)
                      (transport (λ a_6, (a_6 ⬝ (ap ι' h₃)) ⬝ (ap ι' g₃) = _) ((ap_pp ι' h₁ h₂)⁻¹)
                        (transport (λ a_0, a_0 ⬝  (ap ι' g₃) = _)
                          ((concat_pp_p (ap ι' h₁) (ap ι' h₂) (ap ι' h₃))⁻¹)
                          (transport (λ a_0, _ = (ap ι' f₁) ⬝ a_0)
                            ((concat_pp_p (ap ι' i₁) (ap ι' i₂) (ap ι' i₃))⁻¹)
                            (fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₁ w v) u)))))))))))))
     = (fund_dbl_precat_flat_comp₁ (fund_dbl_precat_flat_comp₁ w v) u) :=
  begin
    reverts (u, v, w),
    revert g₃, revert i₃, revert h₃,
    revert g₂, revert i₂, revert h₂,
    revert g₁, revert i₁, revert h₁,
    intro h₁, apply (eq.rec_on h₁),
    intro i₁, apply (eq.rec_on i₁),
    intro g₁,
    intro h₂, apply (eq.rec_on h₂),
    intro i₂, apply (eq.rec_on i₂),
    intro g₂,
    intro h₃, apply (eq.rec_on h₃),
    intro i₃, apply (eq.rec_on i₃),
    intros, apply idp,
  end

  definition fund_dbl_precat_assoc₁ :
    (concat_pp_p i₁ i₂ i₃) ▹ (concat_pp_p h₁ h₂ h₃) ▹
      (fund_dbl_precat_comp₁ w (fund_dbl_precat_comp₁ v u))
    = fund_dbl_precat_comp₁ (fund_dbl_precat_comp₁ w v) u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp1, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp2, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_assoc₁',
    apply moveL_transport_p, apply moveL_transport_p,
    apply moveL_transport_p, apply moveL_transport_p,
    apply moveL_transport_V, apply moveL_transport_V,
    apply moveL_transport_V, apply moveL_transport_V,
    apply inverse,
    apply concat, apply fund_dbl_precat_flat_transp3, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp4, apply moveR_transport_V,
    apply inverse,
    apply fund_dbl_precat_assoc₁_aux,
  end

  definition fund_dbl_precat_id₁ [reducible] {a b : C} (f : ι a = ι b) :
    ap ι' (refl (ι a)) ⬝ ap ι' f = ap ι' f ⬝ ap ι' (refl (ι b)) :=
  concat_1p (ap ι' f)



  definition fund_dbl_precat_id₁_left_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝ (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (ap_pp ι' h (refl c))
      (transport (λ a_6, _ = (ap ι' f) ⬝ a_6) (ap_pp ι' i (refl d))
        (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g) = _) ((concat_p1 h)⁻¹)
          (transport (λ a_6,  _ = (ap ι' f) ⬝ (ap ι' a_6)) ((concat_p1 i)⁻¹) u))))
    = u :=
  begin
    revert u, revert g,
    apply (eq.rec_on i),
    apply (eq.rec_on h),
    intros, apply idp,
  end

  definition fund_dbl_precat_id₁_left (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (concat_p1 i)
     (transport (λ a_4, (ap ι' a_4) ⬝ (ap ι' g) = _) (concat_p1 h)
       (fund_dbl_precat_comp₁ (fund_dbl_precat_id₁ g) u))
    = u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_id₁_left,
    apply inverse, apply fund_dbl_precat_id₁_left_aux,
  end

  definition fund_dbl_precat_id₁_right_aux (a b c d : A)
    (f : a = b) (g : c = d) (h : a = c) (i : b = d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_6, _ =  (ap ι' f) ⬝ a_6) (concat_1p (ap ι' i))
      (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (concat_1p (ap ι' h))
        (transport (λ a_6, a_6 ⬝ (ap ι' g) = _) (ap_pp ι' (refl a) h)
          (transport (λ a_6, _ = (ap ι' f) ⬝ a_6) (ap_pp ι' (refl b) i)
            (transport (λ a_6, (ap ι' a_6) ⬝ (ap ι' g) = _) ((concat_1p h)⁻¹)
              (transport (λ a_6, _ = (ap ι' f) ⬝ (ap ι' a_6)) ((concat_1p i)⁻¹) u))))))
    = u :=
  begin
    revert u,
    revert g, revert i, revert h,
    intro h, apply (eq.rec_on h),
    intro i, apply (eq.rec_on i),
    intros, apply idp,
  end

  definition fund_dbl_precat_id₁_right (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (concat_1p i)
      (transport (λ a_3, (ap ι' a_3) ⬝ (ap ι' g) = _) (concat_1p h)
        (fund_dbl_precat_comp₁ u (fund_dbl_precat_id₁ f))))
    = u :=
  begin
    unfold fund_dbl_precat_comp₁,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_id₁_right',
    apply moveR_transport_V, apply moveR_transport_V,
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
  ((ap_pp ι' g₁ g₂)⁻¹) ▹ ((ap_pp ι' f₁ f₂)⁻¹) ▹
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
    ((ap_pp ι' g₁ g₂)⁻¹) vu)
  = transport (λ a_1, _) ((ap_pp ι' g₁ g₂)⁻¹) (fund_dbl_precat_flat_comp₂ w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' g₁ g₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp6
    (vu : ap ι' h₁ ⬝ (ap ι' g₁ ⬝ ap ι' g₂) = (ap ι' f₁ ⬝ ap ι' f₂) ⬝ ap ι' i₂) :
  fund_dbl_precat_flat_comp₂ w (transport (λ x, _ = x ⬝ _) ((ap_pp ι' f₁ f₂)⁻¹) vu)
  = transport (λ x, _) ((ap_pp ι' f₁ f₂)⁻¹) (fund_dbl_precat_flat_comp₂ w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' f₁ f₂)⁻¹)), apply idp,
  end

  /-definition fund_dbl_precat_flat_transp7
    (wv : ap ι' (h₂ ⬝ h₃) ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, _ = _ ⬝ x) ((ap_pp ι' i₂ i₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' i₂ i₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' i₂ i₃)⁻¹)), apply idp,
  end-/

  /-definition fund_dbl_precat_flat_transp8
    (wv : ap ι' h₂ ⬝ ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_flat_comp₁ (transport (λ x, x ⬝ _ = _) ((ap_pp ι' h₂ h₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' h₂ h₃)⁻¹) (fund_dbl_precat_flat_comp₁ wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' h₂ h₃)⁻¹)), apply idp,
  end-/

  definition fund_dbl_precat_assoc₂ :
    (concat_pp_p g₁ g₂ g₃) ▹ (concat_pp_p f₁ f₂ f₃) ▹
      (fund_dbl_precat_comp₂ w (fund_dbl_precat_comp₂ v u))
    = (fund_dbl_precat_comp₂ (fund_dbl_precat_comp₂ w v) u) :=
  begin
    unfold fund_dbl_precat_comp₂,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp5, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp6, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_assoc₂',
  end

  definition fund_dbl_precat_id₂ [reducible] {a b : C} (f : ι a = ι b) :
    ap ι' f ⬝ ap ι' (refl (ι b)) = ap ι' (refl (ι a)) ⬝ ap ι' f :=
  (concat_1p (ap ι' f))⁻¹

  end

  context
  parameters (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    (ι' : A → X) (ι : C → A)
  include Xtrunc Atrunc Cset

  --set_option pp.implicit true
  set_option pp.notation false
  definition fundamental_dbl_precat : dbl_precat (fundamental_groupoid)
    (λ (a b c d : C) (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d),
      ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :=
  begin
    fapply dbl_precat.mk,
      intros, apply (fund_dbl_precat_comp₁ a_1 a_2),
      intros, apply (@fund_dbl_precat_id₁ X A C Xtrunc Atrunc Cset ι' ι a b f),
      intros, apply fund_dbl_precat_assoc₁,
      intros, apply fund_dbl_precat_id₁_left,
      intros, apply fund_dbl_precat_id₁_right,
      intros, apply succ_is_trunc, apply succ_is_trunc,
      intros, apply (fund_dbl_precat_comp₂ a_1 a_2),
      intros, apply (@fund_dbl_precat_id₂ X A C Xtrunc Atrunc Cset ι' ι a b f),
      intros,
  end
  check dbl_precat.mk
  check @fund_dbl_precat_id₁
  check @fund_dbl_precat_id₁_left


  end
end dbl_gpd
