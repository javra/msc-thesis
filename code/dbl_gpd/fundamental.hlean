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
  definition fund_dbl_precat_comp_flat {a₁ b₁ a₂ b₂ a₃ b₃ : X}
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

  definition fund_dbl_precat_flat_assoc {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    {g₃ : a₄ = b₄} {h₃ : a₃ = a₄} {i₃ : b₃ = b₄}
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
      concat_pp_p i₁ i₂ i₃ ▹ (concat_pp_p h₁ h₂ h₃ ▹
        fund_dbl_precat_comp_flat w (fund_dbl_precat_comp_flat v u))
      = fund_dbl_precat_comp_flat (fund_dbl_precat_comp_flat w v) u :=
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

  definition fund_dbl_precat_flat_assoc' {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    {f₁ : a₁ = b₁} {g₁ : a₂ = b₂} {h₁ : a₁ = a₂} {i₁ : b₁ = b₂}
    {g₂ : a₃ = b₃} {h₂ : a₂ = a₃} {i₂ : b₂ = b₃}
    {g₃ : a₄ = b₄} {h₃ : a₃ = a₄} {i₃ : b₃ = b₄}
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (fund_dbl_precat_flat_assoc w v u))

  definition fund_dbl_precat_flat_id {a b : X} (g : a = b):
    refl a ⬝ g = g ⬝ refl b :=
  concat_1p g

  definition fund_dbl_precat_flat_id_left {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    fund_dbl_precat_comp_flat (fund_dbl_precat_flat_id g) u = u :=
  begin
    revert u, revert f, revert h, revert i,
    apply (eq.rec_on g),
    intro i, apply (eq.rec_on i),
    intros, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_id_right {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :
    transport (λ x, _ = _ ⬝ x) (!concat_1p)
      (transport (λ x, x ⬝ _ = _) (!concat_1p)
        (fund_dbl_precat_comp_flat u (fund_dbl_precat_flat_id f)))
    = u :=
  begin
    revert u, revert f, revert h, revert i,
    apply (eq.rec_on g),
    intro i, apply (eq.rec_on i),
    intro h, apply (eq.rec_on h),
    intros, apply (eq.rec_on u),
    apply idp,
  end

  definition fund_dbl_precat_flat_id_right'  {a b c d : X}
    {f : a = b} {g : c = d} {h : a = c} {i : b = d}
    (u : h ⬝ g = f ⬝ i) :=
  moveL_transport_V _ _ _ _
    (moveL_transport_V _ _ _ _ (fund_dbl_precat_flat_id_right u))


end dbl_gpd

--NON-FLAT VERSIONS
namespace dbl_gpd
  context
  parameters {X A C : Type} [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    {ι' : A → X} {ι : C → A}
    {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {f₁ : ι a₁ = ι b₁} {g₁ : ι a₂ = ι b₂} {h₁ : ι a₁ = ι a₂} {i₁ : ι b₁ = ι b₂}
    {g₂ : ι a₃ = ι b₃} {h₂ : ι a₂ = ι a₃} {i₂ : ι b₂ = ι b₃}
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁)
  include Xtrunc Atrunc Cset
  definition fund_gpd [instance] := (@fundamental_groupoid X A C Xtrunc Atrunc Cset ι)

  definition fund_dbl_precat_comp [reducible]
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      ap ι' (h₁ ⬝ h₂) ⬝ ap ι' g₂ = ap ι' f₁ ⬝ ap ι' (i₁ ⬝ i₂) :=
  ((ap_pp ι' i₁ i₂)⁻¹) ▹ ((ap_pp ι' h₁ h₂)⁻¹) ▹ @fund_dbl_precat_comp_flat X A C Xtrunc Atrunc Cset
    (ι' (ι a₁)) (ι' (ι b₁)) (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₃)) (ι' (ι b₃))
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
    (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) v u

  definition fund_dbl_precat_comp_aux1
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      ((ap_pp ι' h₁ h₂)⁻¹) ▹ fund_dbl_precat_comp_flat v u =
      (ap_pp ι' i₁ i₂) ▹ fund_dbl_precat_comp v u :=
  !transport_pV⁻¹

  definition fund_dbl_precat_comp_aux2_aux
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      (ap_pp ι' h₁ h₂) ▹ ((ap_pp ι' h₁ h₂)⁻¹) ▹ fund_dbl_precat_comp_flat v u =
      (ap_pp ι' h₁ h₂) ▹ (ap_pp ι' i₁ i₂) ▹ fund_dbl_precat_comp v u :=
  ap (transport _ (ap_pp ι' h₁ h₂)) (fund_dbl_precat_comp_aux1 v u)

  definition fund_dbl_precat_comp_aux2_aux2
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      (ap_pp ι' h₁ h₂) ▹ ((ap_pp ι' h₁ h₂)⁻¹) ▹ fund_dbl_precat_comp_flat v u =
      fund_dbl_precat_comp_flat v u :=
  !transport_pV

  definition fund_dbl_precat_comp_aux2
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      (ap_pp ι' h₁ h₂) ▹ (ap_pp ι' i₁ i₂) ▹ fund_dbl_precat_comp v u =
      fund_dbl_precat_comp_flat v u :=
  begin
    apply concat, rotate 1,
    exact (fund_dbl_precat_comp_aux2_aux2 v u),
    exact ((fund_dbl_precat_comp_aux2_aux v u)⁻¹),
  end

  end

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
  fund_dbl_precat_comp_flat w
    (transport (λ a_1, (ap ι' (h₁ ⬝ h₂)) ⬝ (ap ι' g₂) = (ap ι' f₁) ⬝ a_1)
    ((ap_pp ι' i₁ i₂)⁻¹) vu)
  = transport (λ a_1, _) ((ap_pp ι' i₁ i₂)⁻¹) (fund_dbl_precat_comp_flat w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' i₁ i₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp2
    (vu : ap ι' h₁ ⬝ ap ι' h₂ ⬝ ap ι' g₂ = ap ι' f₁ ⬝ (ap ι' i₁ ⬝ ap ι' i₂)) :
  fund_dbl_precat_comp_flat w (transport (λ x, x ⬝ _ = _) ((ap_pp ι' h₁ h₂)⁻¹) vu)
  = transport (λ x, _) ((ap_pp ι' h₁ h₂)⁻¹) (fund_dbl_precat_comp_flat w vu) :=
  begin
    apply (eq.rec_on ((ap_pp ι' h₁ h₂)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp3
    (wv : ap ι' (h₂ ⬝ h₃) ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_comp_flat (transport (λ x, _ = _ ⬝ x) ((ap_pp ι' i₂ i₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' i₂ i₃)⁻¹) (fund_dbl_precat_comp_flat wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' i₂ i₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_flat_transp4
    (wv : ap ι' h₂ ⬝ ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₁ ⬝ (ap ι' i₂ ⬝ ap ι' i₃)) :
  fund_dbl_precat_comp_flat (transport (λ x, x ⬝ _ = _) ((ap_pp ι' h₂ h₃)⁻¹) wv) u
  = transport (λ x, _) ((ap_pp ι' h₂ h₃)⁻¹) (fund_dbl_precat_comp_flat wv u) :=
  begin
    apply (eq.rec_on ((ap_pp ι' h₂ h₃)⁻¹)), apply idp,
  end

  definition fund_dbl_precat_assoc_aux {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : A}
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
                            (fund_dbl_precat_comp_flat (fund_dbl_precat_comp_flat w v) u)))))))))))))
     = (fund_dbl_precat_comp_flat (fund_dbl_precat_comp_flat w v) u) :=
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

  definition fund_dbl_precat_assoc :
    (concat_pp_p i₁ i₂ i₃) ▹ ((concat_pp_p h₁ h₂ h₃) ▹
    fund_dbl_precat_comp w (fund_dbl_precat_comp v u))
    = fund_dbl_precat_comp (fund_dbl_precat_comp w v) u :=
  begin
    unfold fund_dbl_precat_comp,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp1, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp2, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_assoc',
    apply moveL_transport_p, apply moveL_transport_p,
    apply moveL_transport_p, apply moveL_transport_p,
    apply moveL_transport_V, apply moveL_transport_V,
    apply moveL_transport_V, apply moveL_transport_V,
    apply inverse,
    apply concat, apply fund_dbl_precat_flat_transp3, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_transp4, apply moveR_transport_V,
    apply inverse,
    apply fund_dbl_precat_assoc_aux,
  end

  definition fund_dbl_precat_id [reducible] {a b : C} (f : ι a = ι b) :
    ap ι' (refl (ι a)) ⬝ ap ι' f = ap ι' f ⬝ ap ι' (refl (ι b)) :=
  concat_1p (ap ι' f)

  definition fund_dbl_precat_id_left_aux (a b c d : A)
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

  definition fund_dbl_precat_id_left (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (concat_p1 i)
     (transport (λ a_4, (ap ι' a_4) ⬝ (ap ι' g) = _) (concat_p1 h)
       (fund_dbl_precat_comp (fund_dbl_precat_id g) u))
    = u :=
  begin
    unfold fund_dbl_precat_comp,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_id_left,
    apply inverse, apply fund_dbl_precat_id_left_aux,
  end

  definition fund_dbl_precat_id_right_aux (a b c d : A)
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

  definition fund_dbl_precat_id_right (a b c d : C)
    (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d)
    (u : (ap ι' h) ⬝  (ap ι' g) = (ap ι' f) ⬝ (ap ι' i)) :
    (transport (λ a_2, _ = (ap ι' f) ⬝ (ap ι' a_2)) (concat_1p i)
      (transport (λ a_3, (ap ι' a_3) ⬝ (ap ι' g) = _) (concat_1p h)
        (fund_dbl_precat_comp u (fund_dbl_precat_id f))))
    = u :=
  begin
    unfold fund_dbl_precat_comp,
    apply moveR_transport_p, apply moveR_transport_p,
    apply moveR_transport_V, apply moveR_transport_V,
    apply concat, apply fund_dbl_precat_flat_id_right',
    apply moveR_transport_V, apply moveR_transport_V,
    apply inverse, apply fund_dbl_precat_id_right_aux,
  end

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
      intros, apply (fund_dbl_precat_comp a_1 a_2),
      intros, apply (@fund_dbl_precat_id X A C Xtrunc Atrunc Cset ι' ι a b f),
      intros, apply fund_dbl_precat_assoc,
      intros, apply fund_dbl_precat_id_left,
      intros, apply fund_dbl_precat_id_right,
      intros, apply succ_is_trunc, apply succ_is_trunc,
  end
  check dbl_precat.mk
  check @fund_dbl_precat_id
  check @fund_dbl_precat_id_left


  end
end dbl_gpd
