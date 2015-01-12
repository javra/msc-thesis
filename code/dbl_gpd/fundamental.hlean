import algebra.groupoid
import .decl

open dbl_precat precategory truncation eq nat groupoid morphism

namespace dbl_precat
  variables (X A C : Type) (Xtrunc : is_trunc 2 X)
    (Atrunc : is_trunc 1 A) (Cset : is_hset C)
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

  definition fundamental_dbl_precat : dbl_precat (fundamental_groupoid X A C Xtrunc Atrunc Cset ι)
    (λ (a b c d : C) (f : ι a = ι b) (g : ι c = ι d) (h : ι a = ι c) (i : ι b = ι d),
      h ⬝ g = f ⬝ i) :=
  begin
    fapply dbl_precat.mk,
      intros, exact (calc (h₁ ⬝ h₂) ⬝ g₂ = h₁ ⬝ (h₂ ⬝ g₂) : concat_pp_p
                                   ... = h₁ ⬝ (g₁ ⬝ i₂) : a_1
                                   ... = (h₁ ⬝ g₁) ⬝ i₂ : concat_p_pp
                                   ... = (f₁ ⬝ i₁) ⬝ i₂ : a_2
                                   ... = f₁ ⬝ (i₁ ⬝ i₂) : concat_pp_p),
      intros,  exact (calc idp ⬝ f = f : concat_1p
                              ... = f ⬝ idp : concat_p1),
      repeat ( intros ;  apply @is_hset.elim ;  apply succ_is_trunc ; exact Atrunc ),
      intros, exact (calc f₁ ⬝ (i₁ ⬝ i₂) = (f₁ ⬝ i₁) ⬝ i₂ : concat_p_pp
                                    ... = (h₁ ⬝ g₁) ⬝ i₂ : a_2
                                    ... = h₁ ⬝ (g₁ ⬝ i₂) : concat_pp_p
                                    ... = h₁ ⬝ (h₂ ⬝ g₂) : a_1
                                    ... = (h₁ ⬝ h₂) ⬝ g₂ : concat_p_pp),
      intros,  exact (calc f ⬝ idp = f : concat_p1
                              ... = idp ⬝ f : concat_1p),
      repeat ( intros ;  apply @is_hset.elim ;  apply succ_is_trunc ; exact Atrunc ),
      intros, apply succ_is_trunc, apply succ_is_trunc, apply trunc_succ, exact Atrunc,
      repeat ( intros ;  apply @is_hset.elim ;  apply succ_is_trunc ; exact Atrunc ),
  end


end dbl_precat
