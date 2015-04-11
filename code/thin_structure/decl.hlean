import types.pi types.sigma
import ..dbl_cat.decl

open eq dbl_precat category is_trunc

namespace dbl_precat

  variables {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type}
    (D : dbl_precat C D₂)
  include D

  structure thin_structure [class] :=
    (thin : Π ⦃a b c d : D₀⦄
      (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f
      → D₂ f g h i)
    (thin_id₁ : proof Π ⦃a b : D₀⦄ (f : hom a b),
      thin f f (ID a) (ID b) ((id_right f) ⬝ (id_left f)⁻¹) = ID₁ D f qed)
    (thin_id₂ : proof Π ⦃a b : D₀⦄ (f : hom a b),
      thin (ID a) (ID b) f f ((id_left f) ⬝ (id_right f)⁻¹) = ID₂ D f qed)
    (thin_comp₁ : proof Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄
      ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
      ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
      (pv : g₂ ∘ h₂ = i₂ ∘ g₁) (pu : g₁ ∘ h₁ = i₁ ∘ f₁)
      (px : g₂ ∘ h₂ ∘ h₁ = (i₂ ∘ i₁) ∘ f₁),
      comp₁ D (thin g₁ g₂ h₂ i₂ pv) (thin f₁ g₁ h₁ i₁ pu)
      = thin f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁) px qed)
    (thin_comp₂ : proof Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄
      ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
      ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
      (pv : i₂ ∘ g₁ = g₂ ∘ h₂) (pu : i₁ ∘ f₁ = g₁ ∘ h₁)
      (px : (i₂ ∘ i₁) ∘ f₁ = g₂ ∘ h₂ ∘ h₁),
      comp₂ D (thin h₂ i₂ g₁ g₂ pv) (thin h₁ i₁ f₁ g₁ pu)
      = thin (h₂ ∘ h₁) (i₂ ∘ i₁) f₁ g₂ px qed)

end dbl_precat
