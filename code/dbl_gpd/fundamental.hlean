import algebra.groupoid
import .decl

open dbl_precat precategory truncation eq nat groupoid morphism sigma sigma.ops

namespace dbl_precat
  variables (X A C : Type) [Xtrunc : is_trunc 2 X]
    [Atrunc : is_trunc 1 A] [Cset : is_hset C]
    (ι' : A → X) (ι : C → A)
  include Xtrunc Atrunc Cset

  set_option pp.beta true
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

  definition fund_dbl_precat_comp_flat {a₁ b₁ a₂ b₂ a₃ b₃ : X}
    (f₁ : a₁ = b₁) (g₁ : a₂ = b₂) (h₁ : a₁ = a₂) (i₁ : b₁ = b₂)
    (g₂ : a₃ = b₃) (h₂ : a₂ = a₃) (i₂ : b₂ = b₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
      (h₁ ⬝ h₂) ⬝ g₂ = f₁ ⬝ (i₁ ⬝ i₂) :=
    calc (h₁ ⬝ h₂) ⬝ g₂ = h₁ ⬝ (h₂ ⬝ g₂) : concat_pp_p
                   ... = h₁ ⬝ (g₁ ⬝ i₂) : v
                   ... = (h₁ ⬝ g₁) ⬝ i₂ : concat_p_pp
                   ... = (f₁ ⬝ i₁) ⬝ i₂ : u
                   ... = f₁ ⬝ (i₁ ⬝ i₂) : concat_pp_p

  definition fund_dbl_precat_comp [reducible] {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    (f₁ : ι a₁ = ι b₁) (g₁ : ι a₂ = ι b₂) (h₁ : ι a₁ = ι a₂) (i₁ : ι b₁ = ι b₂)
    (g₂ : ι a₃ = ι b₃) (h₂ : ι a₂ = ι a₃) (i₂ : ι b₂ = ι b₃)
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
      ap ι' (h₁ ⬝ h₂) ⬝ ap ι' g₂ = ap ι' f₁ ⬝ ap ι' (i₁ ⬝ i₂) :=
  (!ap_pp⁻¹) ▹ ((!ap_pp⁻¹) ▹ @fund_dbl_precat_comp_flat X A C Xtrunc Atrunc Cset
    (ι' (ι a₁)) (ι' (ι b₁)) (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₃)) (ι' (ι b₃))
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
    (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) v u)

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

  definition fund_dbl_precat_flat_assoc {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : X}
    (f₁ : a₁ = b₁) (g₁ : a₂ = b₂) (h₁ : a₁ = a₂) (i₁ : b₁ = b₂)
    (g₂ : a₃ = b₃) (h₂ : a₂ = a₃) (i₂ : b₂ = b₃)
    (g₃ : a₄ = b₄) (h₃ : a₃ = a₄) (i₃ : b₃ = b₄)
    (w : h₃ ⬝ g₃ = g₂ ⬝ i₃)
    (v : h₂ ⬝ g₂ = g₁ ⬝ i₂)
    (u : h₁ ⬝ g₁ = f₁ ⬝ i₁) :
      concat_pp_p i₁ i₂ i₃ ▹ (concat_pp_p h₁ h₂ h₃ ▹
        fund_dbl_precat_comp_flat X A C f₁ g₂ (h₁ ⬝ h₂) (i₁ ⬝ i₂) g₃ h₃ i₃ w
          (fund_dbl_precat_comp_flat X A C f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u))
      = fund_dbl_precat_comp_flat X A C f₁ g₁ h₁ i₁ g₃ (h₂ ⬝ h₃) (i₂ ⬝ i₃)
        (fund_dbl_precat_comp_flat X A C g₁ g₂ h₂ i₂ g₃ h₃ i₃ w v) u :=
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

  definition fund_dbl_precat_assoc' {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    (f₁ : ι a₁ = ι b₁) (g₁ : ι a₂ = ι b₂) (h₁ : ι a₁ = ι a₂) (i₁ : ι b₁ = ι b₂)
    (g₂ : ι a₃ = ι b₃) (h₂ : ι a₂ = ι a₃) (i₂ : ι b₂ = ι b₃)
    (g₃ : ι a₄ = ι b₄) (h₃ : ι a₃ = ι a₄) (i₃ : ι b₃ = ι b₄)
    (w : ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₂ ⬝ ap ι' i₃)
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
  concat_pp_p (ap ι' i₁) (ap ι' i₂) (ap ι' i₃) ▹
  concat_pp_p (ap ι' h₁) (ap ι' h₂) (ap ι' h₃) ▹
  fund_dbl_precat_comp_flat X A C
    (ap ι' f₁) (ap ι' g₂) (ap ι' h₁ ⬝ ap ι' h₂) (ap ι' i₁ ⬝ ap ι' i₂) (ap ι' g₃) (ap ι' h₃) (ap ι' i₃) w
    (fund_dbl_precat_comp_flat X A C
      (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁) (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) v u)
  = fund_dbl_precat_comp_flat X A C
      (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁) (ap ι' g₃) (ap ι' h₂ ⬝ ap ι' h₃) (ap ι' i₂ ⬝ ap ι' i₃)
      (fund_dbl_precat_comp_flat X A C
        (ap ι' g₁) (ap ι' g₂) (ap ι' h₂) (ap ι' i₂) (ap ι' g₃) (ap ι' h₃) (ap ι' i₃) w v) u :=
  fund_dbl_precat_flat_assoc X A C
    (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁) (ap ι' g₂)
    (ap ι' h₂) (ap ι' i₂) (ap ι' g₃) (ap ι' h₃) (ap ι' i₃) w v u

  check fund_dbl_precat_comp
  definition fund_dbl_precat_assoc''' {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    (f₁ : ι a₁ = ι b₁) (g₁ : ι a₂ = ι b₂) (h₁ : ι a₁ = ι a₂) (i₁ : ι b₁ = ι b₂)
    (g₂ : ι a₃ = ι b₃) (h₂ : ι a₂ = ι a₃) (i₂ : ι b₂ = ι b₃)
    (g₃ : ι a₄ = ι b₄) (h₃ : ι a₃ = ι a₄) (i₃ : ι b₃ = ι b₄)
    (w : ap ι' h₃ ⬝ ap ι' g₃ = ap ι' g₂ ⬝ ap ι' i₃)
    (v : ap ι' h₂ ⬝ ap ι' g₂ = ap ι' g₁ ⬝ ap ι' i₂)
    (u : ap ι' h₁ ⬝ ap ι' g₁ = ap ι' f₁ ⬝ ap ι' i₁) :
  fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₃ (h₂ ⬝ h₃) (i₂ ⬝ i₃)
      (fund_dbl_precat_comp X A C ι' ι g₁ g₂ h₂ i₂ g₃ h₃ i₃ w v) u =
  concat_pp_p i₁ i₂ i₃ ▹ concat_pp_p h₁ h₂ h₃ ▹
  fund_dbl_precat_comp X A C ι' ι f₁ g₂ (h₁ ⬝ h₂) (i₁ ⬝ i₂) g₃ h₃ i₃ w
    (fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u) :=
  --fund_dbl_precat_assoc' X A C ι' ι f₁ g₁ h₁ i₁ g₂ h₂ i₂ g₃ h₃ i₃ w v u
  calc fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₃ (h₂ ⬝ h₃) (i₂ ⬝ i₃)
      (fund_dbl_precat_comp X A C ι' ι g₁ g₂ h₂ i₂ g₃ h₃ i₃ w v) u

    = (!ap_pp⁻¹) ▹ ((!ap_pp⁻¹) ▹ @fund_dbl_precat_comp_flat X A C Xtrunc Atrunc Cset
      (ι' (ι a₁)) (ι' (ι b₁)) (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₄)) (ι' (ι b₄))
      (ap ι' f₁) (ap ι' g₁) (ap ι' h₁) (ap ι' i₁)
      (ap ι' g₃) (ap ι' (h₂ ⬝ h₃)) (ap ι' (i₂ ⬝ i₃))
        ((!ap_pp⁻¹) ▹ ((!ap_pp⁻¹) ▹ @fund_dbl_precat_comp_flat X A C Xtrunc Atrunc Cset
        (ι' (ι a₂)) (ι' (ι b₂)) (ι' (ι a₃)) (ι' (ι b₃)) (ι' (ι a₄)) (ι' (ι b₄))
        (ap ι' g₁) (ap ι' g₂) (ap ι' h₂) (ap ι' i₂)
        (ap ι' g₃) (ap ι' h₃) (ap ι' i₃) w v)) u) : idp

... = concat_pp_p i₁ i₂ i₃ ▹ concat_pp_p h₁ h₂ h₃ ▹
  fund_dbl_precat_comp X A C ι' ι f₁ g₂ (h₁ ⬝ h₂) (i₁ ⬝ i₂) g₃ h₃ i₃ w
    (fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u) : sorry


  definition fundamental_dbl_precat : dbl_precat (fundamental_groupoid X A C ι)
    (λ (a b c d : C) (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d),
      ap ι' h ⬝ ap ι' g = ap ι' f ⬝ ap ι' i) :=
  begin
    fapply dbl_precat.mk,
      intros, apply (fund_dbl_precat_comp X A C ι' ι), exact a_1, exact a_2,
      intros, exact (concat_1p (ap ι' f)),
      intros, apply (fund_dbl_precat_assoc''' X A C ι' ι),
  end
  check dbl_precat.mk

end dbl_precat


      /-intros, exact (calc f₁ ⬝ (i₁ ⬝ i₂) = (f₁ ⬝ i₁) ⬝ i₂ : concat_p_pp
                                    ... = (h₁ ⬝ g₁) ⬝ i₂ : a_2
                                    ... = h₁ ⬝ (g₁ ⬝ i₂) : concat_pp_p
                                    ... = h₁ ⬝ (h₂ ⬝ g₂) : a_1
                                    ... = (h₁ ⬝ h₂) ⬝ g₂ : concat_p_pp),
      intros,  exact (calc f ⬝ idp = f : concat_p1
                              ... = idp ⬝ f : concat_1p),
      repeat ( intros ;  apply @is_hset.elim ;  apply succ_is_trunc ; exact Atrunc ),
      intros, apply succ_is_trunc, apply succ_is_trunc, apply trunc_succ, exact Atrunc,
      repeat ( intros ;  apply @is_hset.elim ;  apply succ_is_trunc ; exact Atrunc ),-/
