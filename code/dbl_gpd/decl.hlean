import algebra.groupoid
import ..dbl_cat.basic ..thin_structure.basic

--open dbl_precat precategory
open eq function iso category dbl_precat is_trunc

context
  parameters
    {D₀ : Type}
    (C : groupoid D₀)
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type)

  definition inv₁_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ g f (h⁻¹) (i⁻¹)

  definition left_inverse₁_type [D : dbl_precat C D₂] (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (left_inverse i) ▹ ((left_inverse h) ▹
    (@comp₁ D₀ C D₂ D a b c d a b f g h i f (h⁻¹) (i⁻¹) (inv₁ u) u)) = ID₁ D₂ f

  definition right_inverse₁_type [D : dbl_precat C D₂] (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (right_inverse i) ▹ ((right_inverse h) ▹
    (@comp₁ D₀ C D₂ D c d a b c d g f (h⁻¹) (i⁻¹) g h i u (inv₁ u))) = ID₁ D₂ g

  definition inv₂_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ (f⁻¹) (g⁻¹) i h

  definition left_inverse₂_type [D : dbl_precat C D₂] (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (left_inverse g) ▹ ((left_inverse f) ▹
    (@comp₂ D₀ C D₂ D _ _ _ _ _ _ _ _ _ _ _ _ _ (inv₂ u) u)) = ID₂ D₂ h

  definition right_inverse₂_type [D : dbl_precat C D₂] (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (right_inverse g) ▹ ((right_inverse f) ▹
    (@comp₂ D₀ C D₂ D _ _ _ _ _ _ _ _ _ _ _ _ _ u (inv₂ u))) = ID₂ D₂ i

end

structure weak_dbl_gpd [class] {D₀ : Type}
  (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type)
  extends D : dbl_precat C D₂ :=
(inv₁ : inv₁_type C D₂)
(left_inverse₁ : @left_inverse₁_type D₀ C D₂ D inv₁)
(right_inverse₁ : @right_inverse₁_type D₀ C D₂ D inv₁)
(inv₂ : inv₂_type C D₂)
(left_inverse₂ : @left_inverse₂_type D₀ C D₂ D inv₂)
(right_inverse₂ : @right_inverse₂_type D₀ C D₂ D inv₂)

structure dbl_gpd [class]  {D₀ : Type}
  (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type)
  extends D : weak_dbl_gpd C D₂:=
(thin : Π ⦃a b c d : D₀⦄
  (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i)
(T : @thin_structure D₀ C D₂ (@weak_dbl_gpd.to_dbl_precat D₀ C D₂ D) thin)

structure Dbl_gpd : Type :=
  (gpd : Groupoid)
  (two_cell : Π ⦃a b c d : gpd⦄ (f : hom a b)
    (g : hom c d) (h : hom a c) (i : hom b d), Type)
  (struct : dbl_gpd gpd two_cell)
  (obj_set : is_hset (carrier gpd)) --TODO: make this all consistent...

attribute Dbl_gpd.struct [instance]
attribute Dbl_gpd.obj_set [instance]
