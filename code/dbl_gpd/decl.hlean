import algebra.groupoid
import ..dbl_cat.basic ..thin_structure.basic

--open dbl_precat precategory
open eq function precategory morphism groupoid dbl_precat

context
  parameters
    {D₀ : Type}
    (C : groupoid D₀)
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type)

  definition inv₁_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ g f (h⁻¹) (i⁻¹)

  definition inverse_compose₁_type [D : dbl_precat C D₂] (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (inverse_compose i) ▹ ((inverse_compose h) ▹
    (@comp₁ D₀ C D₂ D a b c d a b f g h i f (h⁻¹) (i⁻¹) (inv₁ u) u)) = ID₁ D₂ f

  definition compose_inverse₁_type [D : dbl_precat C D₂] (inv₁ : inv₁_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (compose_inverse i) ▹ ((compose_inverse h) ▹
    (@comp₁ D₀ C D₂ D c d a b c d g f (h⁻¹) (i⁻¹) g h i u (inv₁ u))) = ID₁ D₂ g

  definition inv₂_type : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ (f⁻¹) (g⁻¹) i h

  definition inverse_compose₂_type [D : dbl_precat C D₂] (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (inverse_compose g) ▹ ((inverse_compose f) ▹
    (@comp₂ D₀ C D₂ D _ _ _ _ _ _ _ _ _ _ _ _ _ (inv₂ u) u)) = ID₂ D₂ h

  definition compose_inverse₂_type [D : dbl_precat C D₂] (inv₂ : inv₂_type) : Type :=
  Π ⦃a b c d : D₀⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (compose_inverse g) ▹ ((compose_inverse f) ▹
    (@comp₂ D₀ C D₂ D _ _ _ _ _ _ _ _ _ _ _ _ _ u (inv₂ u))) = ID₂ D₂ i

  structure weak_dbl_gpd [class] extends D : dbl_precat C D₂ :=
  (inv₁ : inv₁_type)
  (inverse_compose₁ : @inverse_compose₁_type D inv₁)
  (compose_inverse₁ : @compose_inverse₁_type D inv₁)
  (inv₂ : inv₂_type)
  (inverse_compose₂ : @inverse_compose₂_type D inv₂)
  (compose_inverse₂ : @compose_inverse₂_type D inv₂)
end

context
  parameters
    {D₀ : Type}
    (C : groupoid D₀)
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type)

  structure dbl_gpd [class] extends D : weak_dbl_gpd C D₂:=
  (thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i)
  (T : @thin_structure D₀ C D₂ (@weak_dbl_gpd.to_dbl_precat D₀ C D₂ D) thin)

end
