import algebra.precategory.morphism
import .decl ..thin_structure.basic

open eq dbl_precat precategory is_trunc morphism groupoid

namespace dbl_gpd
  context
  universe variable l
  parameters {D₀ : Type.{l}} [C : groupoid.{l l} D₀]
  {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type.{l}}
  [D : dbl_gpd C D₂]
  {thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i}
  [T : thin_structure D₂ thin]
  include C T

  definition ID₁_inverse_compose ⦃a b : D₀⦄ (f : hom a b) :
    comp₂ D₂ (ID₁ D₂ (f⁻¹)) (ID₁ D₂ f) =
    transport (λ x, D₂ _ x id id) ((left_inverse f)⁻¹)
      (transport (λ x, D₂ x _ id id) ((left_inverse f)⁻¹) (ID₁ D₂ (ID a))) :=
  sorry

  definition ur_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID b) f (f⁻¹) (ID b) :=
  thin (ID b) f (f⁻¹) (ID b) (right_inverse f ⬝ id_left (ID b)⁻¹)

  definition bl_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ f (ID a) (ID a) (f⁻¹) :=
  thin f (ID a) (ID a) (f⁻¹) (id_left (ID a) ⬝ (left_inverse f)⁻¹)

  end
end dbl_gpd
