import .morphism

open xmod category function eq is_trunc

namespace xmod

  universe variables l₁ l₂ l₃
  definition cat_xmod : precategory.{(max l₁ l₂ l₃)+1 (max l₁ l₂ l₃)} Xmod.{l₁ l₂ l₃} :=
  begin
    fapply precategory.mk,
      intros [X, Y], apply (xmod_morphism X Y),
      intros [X, Y], apply xmod_morphism_hset,
      intros [X, Y, Z, g, f], apply (xmod_morphism_comp g f),
      intro X, apply xmod_morphism_id,
      intros [X, Y, Z, W, h, g, f], apply xmod_morphism_assoc,
      intros [X, Y, f], apply xmod_morphism_id_left,
    intros [X, Y, f], apply xmod_morphism_id_right,
  end

  attribute cat_xmod [instance]

  definition Cat_xmod [reducible] : Precategory :=
  Precategory.mk Xmod cat_xmod

end xmod
