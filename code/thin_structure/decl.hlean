import types.pi types.sigma
import ..dbl_cat.decl ..dbl_cat.basic

open eq dbl_precat precategory truncation morphism

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) [D : dbl_precat C D₂]

  set_option unifier.max_steps 23574
  set_option pp.beta true
  structure thin_structure (thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i) : Type :=
  (thin_id₁ : Π ⦃a b : D₀⦄ (f : hom a b) p, thin f f (ID a) (ID b) p = ID₁ D₂ f)
  (thin_id₂ : Π ⦃a b : D₀⦄ (f : hom a b) p, thin (ID a) (ID b) f f p = ID₂ D₂ f)
  (thin_comp₁ : Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄ ⦃f₁ : @hom D₀ C a b⦄ ⦃g₁ : @hom D₀ C c₁ d₁⦄
    ⦃h₁ : @hom D₀ C a c₁⦄ ⦃i₁ : @hom D₀ C b d₁⦄
    ⦃g₂ : @hom D₀ C c₂ d₂⦄ ⦃h₂ : @hom D₀ C c₁ c₂⦄ ⦃i₂ : @hom D₀ C d₁ d₂⦄
    (pv : @compose D₀ C c₁ c₂ d₂ g₂ h₂ = @compose D₀ C c₁ d₁ d₂ i₂ g₁)
    (pu : @compose D₀ C a c₁ d₁ g₁ h₁ = @compose D₀ C a b d₁ i₁ f₁)
    (px : @compose D₀ C a c₂ d₂ g₂ (@compose D₀ C a c₁ c₂ h₂ h₁)
      = @compose D₀ C a b d₂ (@compose D₀ C b d₁ d₂ i₂ i₁) f₁),
    @comp₁ D₀ C D₂ D a b c₁ d₁ c₂ d₂ f₁ g₁ h₁ i₁ g₂ h₂ i₂
      (@thin c₁ d₁ c₂ d₂ g₁ g₂ h₂ i₂ pv)
      (@thin a b c₁ d₁ f₁ g₁ h₁ i₁ pu) =
    @thin a b c₂ d₂ f₁ g₂ (@compose D₀ C a c₁ c₂ h₂ h₁) (@compose D₀ C b d₁ d₂ i₂ i₁) px)
  (thin_comp₂ : Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄ ⦃f₁ : @hom D₀ C a b⦄ ⦃g₁ : @hom D₀ C c₁ d₁⦄
    ⦃h₁ : @hom D₀ C a c₁⦄ ⦃i₁ : @hom D₀ C b d₁⦄
    ⦃g₂ : @hom D₀ C c₂ d₂⦄ ⦃h₂ : @hom D₀ C c₁ c₂⦄ ⦃i₂ : @hom D₀ C d₁ d₂⦄
    (pv : @compose D₀ C c₁ d₁ d₂ i₂ g₁ = @compose D₀ C c₁ c₂ d₂ g₂ h₂)
    (pu : @compose D₀ C a b d₁ i₁ f₁ = @compose D₀ C a c₁ d₁ g₁ h₁)
    (px : @compose D₀ C a b d₂ (@compose D₀ C b d₁ d₂ i₂ i₁) f₁
      = @compose D₀ C a c₂ d₂ g₂ (@compose D₀ C a c₁ c₂ h₂ h₁)),
    @comp₂ D₀ C D₂ D a b c₁ d₁ c₂ d₂ f₁ g₁ h₁ i₁ g₂ h₂ i₂
      (@thin c₁ c₂ d₁ d₂ h₂ i₂ g₁ g₂ pv)
      (@thin a c₁ b d₁ h₁ i₁ f₁ g₁ pu) =
    @thin a c₂ b d₂ (@compose D₀ C a c₁ c₂ h₂ h₁) (@compose D₀ C b d₁ d₂ i₂ i₁) f₁ g₂ px)

end dbl_precat
