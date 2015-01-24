import algebra.groupoid
import ..dbl_cat.basic ..thin_structure.basic

--open dbl_precat precategory
open eq function precategory morphism groupoid dbl_precat

structure weak_dbl_gpd' [class] {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends parent: dbl_precat C D₂ :=
  (all_iso₁ : Π (a b : worm_precat.two_cell_ob)
    (f : @precategory.hom _ (@vert_precat D₀ C D₂ parent) a b),
      @is_iso worm_precat.two_cell_ob (@vert_precat D₀ C D₂ parent) a b f)

structure weak_dbl_gpd [class] {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends parent : weak_dbl_gpd' C D₂ :=
  (all_iso₂ : Π (a b : worm_precat.two_cell_ob)
    (f : @precategory.hom _ (@horiz_precat D₀ C D₂ parent) a b),
      @is_iso worm_precat.two_cell_ob (@horiz_precat D₀ C D₂ parent) a b f)

structure dbl_gpd [class] {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends parent : weak_dbl_gpd' C D₂ :=
  (thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i)
  (T : @thin_structure D₀ C D₂ parent thin)
