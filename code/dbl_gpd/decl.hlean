import algebra.groupoid
import ..dbl_cat.basic

--open dbl_precat precategory
open eq function precategory morphism groupoid dbl_precat

namespace weak_dbl_gpd

check dbl_precat
structure weak_dbl_gpd [class] {D₀ : Type} (C : groupoid D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) extends dbl_precat C D₂ :=
  (inv₁ : Π ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ g f (h⁻¹) (i⁻¹))
/-
  (iso₁_sect : Π ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i),
    (transport (λ x, D₂ f f (ID a) x) (inverse_compose i)
      (transport (λ x, D₂ f f x (i⁻¹ ∘ i)) (inverse_compose h)
        (comp₁ (inv₁ u) u))) = ID₁ D₂ f)
exit
  (iso₁_retr : Π ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i), comp₁ u (inv₁ u) = ID₁ g)
exit
  (inv₂ : Π ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d},
    D₂ f g h i → D₂ (f⁻¹) (g⁻¹) i h)
  (iso₂_sect : Π ⦃ a b c d : D₀ ⦄ {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : D₂ f g h i), comp₂ (inv₂ u) u = ID₂ f)-/

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
