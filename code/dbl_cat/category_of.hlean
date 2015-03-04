import .decl .functor
import algebra.category.basic
set_option pp.beta true

open eq is_trunc Dbl_precat category equiv prod sigma pi functor

namespace dbl_precat

  set_option apply.class_instance false
  definition is_hset_dbl_functor (D E : Dbl_precat) (Dset : is_hset (carrier (cat E))) :
    is_hset (dbl_functor D E) :=
  begin
    apply is_trunc_equiv_closed,
      apply (dbl_functor_sigma_char D E),
    apply is_trunc_sigma, apply functor.is_hset_functor, intro catF,
    apply is_trunc_sigma,
      repeat ( apply is_trunc_pi ; intros), apply (homH' (two_cell E)), intro twoF,
    repeat ( apply is_trunc_prod ;
      repeat ( apply is_trunc_pi ; intros) ; apply is_trunc_eq ;
      apply is_trunc_succ ; apply (homH' (two_cell E)) ),
    repeat ( apply is_trunc_pi ; intros), apply is_trunc_eq,
      apply is_trunc_succ, apply (homH' (two_cell E)),
  end

  --set_option pp.implicit true
  universe variables l₁ l₂ l₃
  definition cat_dbl_precat : category.{(max l₁ l₂ l₃)+1 (max l₁ l₂ l₃)}
    Dbl_precat.{l₁ l₂ l₃} :=
  begin
    fapply category.mk,
      intros (D, E), apply (dbl_functor D E),
      intros (D, E), apply (is_hset_dbl_functor D E),
      apply obj_set,
      intros (C, D, E, G, F), apply (dbl_functor_compose G F),
      intro D, apply (dbl_functor_id D),
      intros (B, C, D, E, H, G, F),
        --fapply (dbl_functor.congr B E),
          --apply functor.assoc,
          --repeat ( apply eq_of_homotopy ; intros),

  end

end dbl_precat
