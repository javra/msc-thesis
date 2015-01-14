import algebra.groupoid
import ..dbl_cat.basic

--open dbl_precat precategory
open eq function precategory morphism groupoid dbl_precat

namespace weak_dbl_gpd

check @dbl_precat.vert_precat
check @dbl_precat.horiz_precat
check @hom
check dbl_precat.mk
check @is_iso

structure weak_dbl_gpd [class] {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends dbl_precat C D₂ :=
  (all_iso₁ : Π a b (f : @precategory.hom _
    (@vert_precat D₀ C D₂
       (dbl_precat.mk @comp₁ @ID₁ @assoc₁ @id_left₁ @id_right₁ @homH'
         @comp₂ @ID₂ @assoc₂ @id_left₂ @id_right₂ @homH'_dontuse
         @id_comp₁ @id_comp₂ @interchange
       )
    )
    a b), @is_iso _
            (@vert_precat D₀ C D₂
              (dbl_precat.mk @comp₁ @ID₁ @assoc₁ @id_left₁ @id_right₁ @homH'
                @comp₂ @ID₂ @assoc₂ @id_left₂ @id_right₂ @homH'_dontuse
                @id_comp₁ @id_comp₂ @interchange)
              )
            a b f)
exit
structure weak_dbl_gpd' [class]  {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends weak_dbl_gpd C D₂ :=
  (all_iso₂ : Π a b (f : @precategory.hom _
    (@horiz_precat D₀ C D₂
       (dbl_precat.mk @comp₁ @ID₁ @assoc₁ @id_left₁ @id_right₁ @homH'
         @comp₂ @ID₂ @assoc₂ @id_left₂ @id_right₂ @homH'_dontuse
         @id_comp₁ @id_comp₂ @interchange
       )
    )
    a b), @is_iso _
            (@horiz_precat D₀ C D₂
              (dbl_precat.mk @comp₁ @ID₁ @assoc₁ @id_left₁ @id_right₁ @homH'
                @comp₂ @ID₂ @assoc₂ @id_left₂ @id_right₂ @homH'_dontuse
                @id_comp₁ @id_comp₂ @interchange)
              )
            a b f)



exit

end weak_dbl_gpd

open weak_dbl_gpd

namespace weak_dbl_gpd

  variables {D₀ : Type} (C : groupoid D₀)
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type) (D : weak_dbl_gpd C D₂)

  variables ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i)

  check ID₁

  check ((transport (λ x, D₂ f f (ID a) x) (inverse_compose i)
      (transport (λ x, D₂ f f x (i⁻¹ ∘ i)) (inverse_compose h)
        (comp₁ C (weak_dbl_gpd.inv₁ C u) u))) = ID₁ D₂ f)

end weak_dbl_gpd

check @weak_dbl_gpd.weak_dbl_gpd
