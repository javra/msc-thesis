import algebra.precategory.basic

open precategory morphism

namespace dbl_precat
  variables {D₀ : Type} (C : precategory D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) (D : dbl_precat C D₂)
  include C D

  definition D₁ : D₀ → D₀ → Type := @hom D₀ C

  definition horiz_precat : precategory (Σ (a b : D₀), hom a b) :=
  begin

  end

  notation u `+₁` v := comp₁ v u
  notation u `+₂` v := comp₂ v u

  check D₁
  variables (a b₁ b₂ c d₁ d₂ : D₀) (f₁ : hom a b₁)
    (g₁ : hom c d₁) (h : hom a c)
    (i₁ : hom b₁ d₁) (f₂ : hom b₁ b₂)
    (g₂ : hom d₁ d₂) (i₂ : hom b₂ d₂)
    (u : D₂ f₁ g₁ h i₁)
    (v : D₂ f₂ g₂ i₁ i₂)


end dbl_precat
