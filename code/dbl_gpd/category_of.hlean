import .functor
import algebra.category.basic

open eq function is_trunc Dbl_gpd category equiv prod sigma pi functor

namespace dbl_gpd

  set_option apply.class_instance false
  definition is_hset_dbl_functor (D E : Dbl_gpd) : is_hset (dbl_functor D E) :=
  begin
    apply is_trunc_equiv_closed,
      apply (dbl_functor_sigma_char D E),
    apply is_trunc_sigma,
      apply @functor.is_hset_functor, apply (Dbl_gpd.obj_set E), intro catF,
    apply is_trunc_sigma,
      repeat ( apply is_trunc_pi ; intros), apply (homH' E), intro twoF,
    repeat ( apply is_trunc_prod ;
      repeat ( apply is_trunc_pi ; intros) ; apply is_trunc_eq ;
      apply is_trunc_succ ; apply (homH' E)),
    repeat ( apply is_trunc_pi ; intros), apply is_trunc_eq,
      apply is_trunc_succ, apply (homH' E),
  end

  universe variables l₁ l₂ l₃
  definition cat_dbl_gpd [reducible] : precategory.{(max l₁ l₂ l₃)+1 (max l₁ l₂ l₃)}
    Dbl_gpd.{l₁ l₂ l₃} :=
  begin
    fapply precategory.mk,
      intros [D, E], apply (dbl_functor D E),
      intros [D, E], apply (is_hset_dbl_functor D E),
      intros [C, D, E, G, F], apply (dbl_functor.compose G F),
      intro D, apply (dbl_functor.id D),
      intros [B, C, D, E, H, G, F], apply (dbl_functor.assoc),
      intros [B, C, F], apply (dbl_functor.id_left),
      intros [B, C, F], apply (dbl_functor.id_right),
  end

  definition Cat_dbl_gpd [reducible] : Precategory :=
  Precategory.mk Dbl_gpd cat_dbl_gpd

end dbl_gpd
