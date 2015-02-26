import .decl .functor
import algebra.category.basic
set_option pp.beta true

open eq morphism is_trunc Dbl_precat Precategory equiv prod sigma pi functor

namespace dbl_precat

  set_option apply.class_instance false
  definition is_hset_dbl_functor (D E : Dbl_precat) (Dset : is_hset (objects (cat E))) :
    is_hset (dbl_functor D E) :=
  begin
    apply is_trunc_equiv_closed,
      apply (dbl_functor_sigma_char D E),
    apply is_trunc_sigma, apply functor.strict_cat_has_functor_hset, intro catF,
    apply is_trunc_sigma,
      repeat ( apply is_trunc_pi ; intros), apply (homH' (two_cell E)), intro twoF,
    repeat ( apply is_trunc_prod ;
      repeat ( apply is_trunc_pi ; intros) ; apply is_trunc_eq ;
      apply is_trunc_succ ; apply (homH' (two_cell E)) ),
    repeat ( apply is_trunc_pi ; intros), apply is_trunc_eq,
      apply is_trunc_succ, apply (homH' (two_cell E)),
  end

  --set_option pp.universes true
  universe variables l₁ l₂ l₃
  check dbl_functor_compose
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
  end

end dbl_precat
