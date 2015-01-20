import types.pi types.sigma
import .decl

open eq dbl_precat precategory truncation morphism

namespace dbl_precat
  context
  parameters {D₀ : Type} [C : precategory D₀]
  {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type} [D : dbl_precat C D₂]
  {thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i}
  [T : thin_structure D₂ thin]
  include D T

  definition br_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ f (ID b) f (ID b) :=
  thin f (ID b) f (ID b) idp

  definition ul_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID a) f (ID a) f :=
  thin (ID a) f (ID a) f idp

  set_option pp.beta true
  set_option pp.implicit true
  check comp₂
  definition ID_of_ul_br ⦃a b : D₀⦄ (f : hom a b) :
    comp₂ D₂ (br_connect f) (ul_connect f) = (id_left f)⁻¹ ▹ (id_right f)⁻¹ ▹ ID₁ D₂ f :=
  sorry


end dbl_precat
