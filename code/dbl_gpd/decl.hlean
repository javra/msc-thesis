import algebra.category.groupoid
import ..dbl_cat.basic ..thin_structure.basic

--open dbl_precat precategory
open eq function iso category dbl_precat is_trunc

section
  parameters
    {D₀ : Type}
    (C : groupoid D₀)
    (D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c →  hom b d → Type)
    (D : dbl_precat C D₂)

  definition inv₁_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ g f (h⁻¹) (i⁻¹)

  definition left_inverse₁_type (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (left_inverse i) ▸ (left_inverse h) ▸ (comp₁ D (inv₁ u) u) = ID₁ D f

  definition right_inverse₁_type (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (right_inverse i) ▸ (right_inverse h) ▸ (comp₁ D u (inv₁ u)) = ID₁ D g

  definition inv₂_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ (f⁻¹) (g⁻¹) i h

  definition left_inverse₂_type (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (left_inverse g) ▸ (left_inverse f) ▸ (comp₂ D (inv₂ u) u) = ID₂ D h

  definition right_inverse₂_type (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (right_inverse g) ▸ (right_inverse f) ▸ (comp₂ D u (inv₂ u)) = ID₂ D i

end

structure weak_dbl_gpd {D₀ : Type}
  (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c →  hom b d → Type)
  extends D : dbl_precat C D₂ :=
  (inv₁ : inv₁_type C D₂)
  (left_inverse₁ : left_inverse₁_type C D₂ D inv₁)
  (right_inverse₁ : right_inverse₁_type C D₂ D inv₁)
  (inv₂ : inv₂_type C D₂)
  (left_inverse₂ : left_inverse₂_type C D₂ D inv₂)
  (right_inverse₂ : right_inverse₂_type C D₂ D inv₂)

structure dbl_gpd {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c →  hom b d → Type)
  extends D : weak_dbl_gpd C D₂ :=
  (T : thin_structure (weak_dbl_gpd.to_dbl_precat D))

attribute dbl_gpd.T [instance]

structure Dbl_gpd : Type :=
  (gpd : Groupoid)
  (two_cell : Π ⦃a b c d : gpd⦄, hom a b → hom c d → hom a c →  hom b d → Type)
  (struct : dbl_gpd gpd two_cell)
  (obj_set : is_hset (carrier gpd))

attribute Dbl_gpd.obj_set [instance]
attribute Dbl_gpd.struct [coercion]
