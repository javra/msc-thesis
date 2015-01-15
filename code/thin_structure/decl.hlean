import types.pi types.sigma
import .decl .basic

open eq dbl_precat precategory truncation morphism

namespace dbl_precat
  variables {D₀ : Type} [C : precategory D₀]
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type) [D : dbl_precat C D₂]

  set_option unifier.max_steps 100000
  set_option verbose true
  check @comp₂
  structure thin_structure (thin : Π ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄, D₂ f g h i → Type) : Type :=
  (thin_hprop : Π ⦃a b c d : D₀⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i), is_hprop (thin u))
  (thin_id₁ : Π ⦃a b : D₀⦄ (f : hom a b), thin (ID₁ D₂ f))
  (thin_id₂ : Π ⦃a b : D₀⦄ (f : hom a b), thin (ID₂ D₂ f))
  (thin_comm_sel :  Π ⦃a b c d : D₀⦄ (f : @hom D₀ C a b) (g : @hom D₀ C c d)
    (h : @hom D₀ C a c) (i : @hom D₀ C b d), g ∘ h = i ∘ f → D₂ f g h i)
  (thin_comm_thin : Π ⦃a b c d : D₀⦄ (f : @hom D₀ C a b) (g : @hom D₀ C c d)
    (h : @hom D₀ C a c) (i : @hom D₀ C b d)
    (u : D₂ f g h i) (p : @compose D₀ C a c d g h = @compose D₀ C a b d i f),
      thin (thin_comm_sel f g h i p))
  (thin_comp₁ : Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄ ⦃f₁ : @hom D₀ C a b⦄ ⦃g₁ : @hom D₀ C c₁ d₁⦄
    ⦃h₁ : @hom D₀ C a c₁⦄ ⦃i₁ : @hom D₀ C b d₁⦄
    ⦃g₂ : @hom D₀ C c₂ d₂⦄ ⦃h₂ : @hom D₀ C c₁ c₂⦄ ⦃i₂ : @hom D₀ C d₁ d₂⦄
    {v : D₂ g₁ g₂ h₂ i₂} {u : D₂ f₁ g₁ h₁ i₁},
    @thin c₁ d₁ c₂ d₂ g₁ g₂ h₂ i₂ v
    → @thin a b c₁ d₁ f₁ g₁ h₁ i₁ u
    → @thin a b c₂ d₂ f₁ g₂ (@compose D₀ C a c₁ c₂ h₂ h₁) (@compose D₀ C b d₁ d₂ i₂ i₁)
         (@comp₁ D₀ C D₂ D a b c₁ d₁ c₂ d₂ f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u))
  (thin_comp₂ : Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄ ⦃f₁ : @hom D₀ C a b⦄ ⦃g₁ : @hom D₀ C c₁ d₁⦄
    ⦃h₁ : @hom D₀ C a c₁⦄ ⦃i₁ : @hom D₀ C b d₁⦄
    ⦃g₂ : @hom D₀ C c₂ d₂⦄ ⦃h₂ : @hom D₀ C c₁ c₂⦄ ⦃i₂ : @hom D₀ C d₁ d₂⦄
    {v : @D₂ c₁ c₂ d₁ d₂ h₂ i₂ g₁ g₂} {u : @D₂ a c₁ b d₁ h₁ i₁ f₁ g₁},
    @thin c₁ c₂ d₁ d₂ h₂ i₂ g₁ g₂ v
    → @thin a c₁ b d₁ h₁ i₁ f₁ g₁ u
    → @thin a c₂ b d₂ (@compose D₀ C a c₁ c₂ h₂ h₁) (@compose D₀ C b d₁ d₂ i₂ i₁) f₁ g₂
         (@comp₂ D₀ C D₂ D a b c₁ d₁ c₂ d₂ f₁ g₁ h₁ i₁ g₂ h₂ i₂ v u))

end dbl_precat
