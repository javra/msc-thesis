import algebra.groupoid
import .decl

open dbl_precat precategory truncation eq nat groupoid morphism

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

  definition fund_dbl_precat_comp {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    (f₁ : ι a₁ = ι b₁) (g₁ : ι a₂ = ι b₂) (h₁ : ι a₁ = ι a₂) (i₁ : ι b₁ = ι b₂)
    (g₂ : ι a₃ = ι b₃) (h₂ : ι a₂ = ι a₃) (i₂ : ι b₂ = ι b₃)
    (v : ap ι' (h₂ ⬝ g₂) = ap ι' (g₁ ⬝ i₂)) (u : ap ι' (h₁ ⬝ g₁) = ap ι' (f₁ ⬝ i₁)) :
      ap ι' ((h₁ ⬝ h₂) ⬝ g₂) = ap ι' (f₁ ⬝ (i₁ ⬝ i₂)) :=
  calc ap ι' ((h₁ ⬝ h₂) ⬝ g₂) = ap ι' (h₁ ⬝ (h₂ ⬝ g₂)) : concat_pp_p
                         ... = (ap ι' h₁) ⬝ (ap ι' (h₂ ⬝ g₂)) : ap_pp
                         ... = (ap ι' h₁) ⬝ (ap ι' (g₁ ⬝ i₂)) : v
                         ... = (ap ι' (h₁ ⬝ (g₁ ⬝ i₂))) : ap_pp
                         ... = (ap ι' ((h₁ ⬝ g₁) ⬝ i₂)) : concat_p_pp
                         ... = (ap ι' (h₁ ⬝ g₁)) ⬝ (ap ι' i₂) : ap_pp
                         ... = (ap ι' (f₁ ⬝ i₁)) ⬝ (ap ι' i₂) : u
                         ... = (ap ι' ((f₁ ⬝ i₁) ⬝ i₂)) : ap_pp
                         ... = (ap ι' (f₁ ⬝ (i₁ ⬝ i₂))) : concat_pp_p

  /-
  definition fund_dbl_precat_assoc {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : C}
    (f₁ : ι a₁ = ι b₁) (g₁ : ι a₂ = ι b₂) (h₁ : ι a₁ = ι a₂) (i₁ : ι b₁ = ι b₂)
    (g₂ : ι a₃ = ι b₃) (h₂ : ι a₂ = ι a₃) (i₂ : ι b₂ = ι b₃)
    (g₃ : ι a₄ = ι b₄) (h₃ : ι a₃ = ι a₄) (i₃ : ι b₃ = ι b₄)
    (w : ap ι' (h₃ ⬝ g₃) = ap ι' (g₂ ⬝ i₃))
    (v : ap ι' (h₂ ⬝ g₂) = ap ι' (g₁ ⬝ i₂))
    (u : ap ι' (h₁ ⬝ g₁) = ap ι' (f₁ ⬝ i₁)) :
    transport (λ x, ap ι' (_ ⬝ g₃) = ap ι' (f₁ ⬝ x)) (assoc i₃ i₂ i₁)
      (transport (λ x, ap ι' (x ⬝ g₃) = ap ι' (f₁ ⬝ _)) (assoc h₃ h₂ h₁)
      (fund_dbl_precat_comp X A C ι' ι f₁ g₂ (h₁ ⬝ h₂) (i₁ ⬝ i₂) g₃ h₃ i₃ w
        (fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u)))
      = fund_dbl_precat_comp X A C ι' ι f₁ g₁ h₁ i₁ g₃ (h₂ ⬝ h₃) (i₂ ⬝ i₃)
        (fund_dbl_precat_comp X A C ι' ι g₁ g₂ h₂ i₂ g₃ h₃ i₃ w v) u :=
  begin

  end-/

  definition fundamental_dbl_precat : dbl_precat (fundamental_groupoid X A C ι)
    (λ (a b c d : C) (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d),
      ap ι' (h ⬝ g) = ap ι' (f ⬝ i)) :=
  begin
    fapply dbl_precat.mk,
      intros, apply (fund_dbl_precat_comp X A C ι' ι), exact a_1, exact a_2,
      intros, exact (calc ap ι' (idp ⬝ f) = ap ι' f : concat_1p
                                      ... = ap ι' (f ⬝ idp) : concat_p1),
      intros, apply (eq.rec_on u),
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
