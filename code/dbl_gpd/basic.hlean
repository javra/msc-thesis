import .decl ..thin_structure.basic

open eq dbl_precat iso category is_trunc

namespace dbl_gpd
  context
  universe variable l
  parameters {D₀ : Type.{l}} [C : groupoid.{l l} D₀]
  {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type.{l}}
  [D : dbl_gpd C D₂]
  include C D

  definition ID₁_inverse_compose ⦃a b : D₀⦄ (f : hom a b) :
    comp₂ D₂ (ID₁ D₂ (f⁻¹)) (ID₁ D₂ f) =
    transport (λ x, D₂ _ x id id) ((left_inverse f)⁻¹)
      (transport (λ x, D₂ x _ id id) ((left_inverse f)⁻¹) (ID₁ D₂ (ID a))) :=
  sorry

  definition ur_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID b) f (f⁻¹) (ID b) :=
  thin D₂ (ID b) f (f⁻¹) (ID b) (right_inverse f ⬝ (id_left (ID b))⁻¹)

  definition ur_connect' ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID a) (f⁻¹) f (ID a) :=
  thin D₂ (ID a) (f⁻¹) f (ID a) (left_inverse f ⬝ (id_left (ID a))⁻¹)

  definition bl_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ f (ID a) (ID a) (f⁻¹) :=
  thin D₂ f (ID a) (ID a) (f⁻¹) (id_left (ID a) ⬝ (left_inverse f)⁻¹)

  definition bl_connect' ⦃a b : D₀⦄ (f : hom a b) : D₂ (f⁻¹) (ID b) (ID b) f :=
  thin D₂ (f⁻¹) (ID b) (ID b) f (id_left (ID b) ⬝ (right_inverse f)⁻¹)

  --TODO: show that bl_connect and bl_connect' are related...

  end
end dbl_gpd
