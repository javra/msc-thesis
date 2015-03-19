import .morphism

open xmod category function eq is_trunc

namespace xmod

  universe variables l1 l2 l3
  definition cat_xmod : precategory.{(max l1 l2 l3)+1 (max l1 l2 l3)} Xmod.{l1 l2 l3} :=
  begin
    fapply precategory.mk,
      intros (X, Y), apply (xmod_morphism X Y),
      intros (X, Y), apply xmod_morphism_hset,
      intros (X, Y, Z, g, f), apply (xmod_morphism_comp g f),
      intro X, apply xmod_morphism_id,
      intros (X, Y, Z, W, h, g, f), apply xmod_morphism_assoc,
      intros (X, Y, f), apply xmod_morphism_id_left,
    intros (X, Y, f), apply xmod_morphism_id_right,
  end

  definition Cat_xmod [reducible] : Precategory :=
  Precategory.mk Xmod cat_xmod

end xmod
