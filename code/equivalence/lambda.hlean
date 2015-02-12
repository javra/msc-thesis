import ..dbl_gpd.decl ..xmod.decl
set_option apply.class_instance false -- turn off class instance resolution by apply tactic

open eq sigma unit groupoid precategory morphism path_algebra xmod

namespace lambda
  context
  parameters {P₀ : Type} [P : groupoid P₀] (M: P₀ → Group) [MM : xmod M]
  include P MM

  structure lambda_morphism ⦃a b c d : P₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d) :=
  (m : M d) (comm : μ P m = i ∘ f ∘ h⁻¹ ∘ g⁻¹)

  --set_option pp.notation false
  --set_option pp.implicit true
  protected definition lambda_morphism_comp₁ ⦃a b c₁ d₁ c₂ d₂⦄
    ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : lambda_morphism g₁ g₂ h₂ i₂) (u : lambda_morphism f₁ g₁ h₁ i₁) :
  lambda_morphism f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁) :=
  begin
    apply (lambda_morphism.rec_on v), intros (m_v, comm_v),
    apply (lambda_morphism.rec_on u), intros (m_u, comm_u),
    fapply lambda_morphism.mk,
      exact ((φ i₂ m_u) * m_v),
      apply concat, apply μ_respect_comp,
      apply concat, apply (ap (λ x, _ ∘ x)), apply comm_v,
      apply concat, apply (ap (λ x, x ∘ _)), apply CM1,
      apply concat, apply (ap (λ x, (_ ∘ x ∘ _) ∘ _)), apply comm_u,
      apply concat, apply (!assoc⁻¹),
      apply concat, rotate 1, apply assoc, apply (ap (λ x, comp i₂ x)),
      apply concat, apply inverse, apply assoc,
      apply concat, apply inverse, apply assoc, apply (ap (λ x, comp i₁ x)),
      apply concat, apply inverse, apply assoc, apply (ap (λ x, comp f₁ x)),
      apply concat, apply (ap (λ x, comp _ x)), apply assoc,
      apply concat, apply (ap (λ x, comp _ x)), apply (ap (λ x, comp x _)),
        apply inverse_compose,
      apply concat, apply (ap (λ x, comp _ x)), apply id_left,
      apply concat, apply assoc,
      apply concat, apply (ap (λ x, comp x _)), apply (!assoc⁻¹),
      apply concat, apply (ap (λ x, comp x _)), apply (ap (λ x, comp _ x)),
        apply inverse_compose,
      apply concat, apply (ap (λ x, comp x _)), apply id_right,
      apply concat, apply assoc, apply (ap (λ x, comp x _)),
      apply inverse, apply inv_pp,
  end

  check dbl_gpd
  protected definition dbl_gpd : dbl_gpd P lambda_morphism :=
  begin
    fapply dbl_gpd.mk,
      intros,
  end

  end
end lambda
