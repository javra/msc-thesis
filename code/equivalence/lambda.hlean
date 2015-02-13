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

  --TODO why does this need that many steps?
  set_option unifier.max_steps 50000
  protected definition lambda_morphism.congr ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {m1 m2 : M d} (comm1 : μ P m1 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (comm2 : μ P m2 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (p1 : m1 = m2) (p2 : p1 ▹ comm1 = comm2) :
    (lambda_morphism.mk m1 comm1) = (lambda_morphism.mk m2 comm2) :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1), apply idp,
  end
  set_option unifier.max_steps 20000


  protected definition lambda_morphism_comp₁ ⦃a b c₁ d₁ c₂ d₂ : P₀⦄
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
    apply inverse, apply iso.inv_pp,
  end

  protected definition lambda_morphism.ID₁ ⦃a b : P₀⦄ (f : hom a b) :
    lambda_morphism f f id id :=
  begin
    fapply lambda_morphism.mk,
      apply 1,
    apply concat, apply μ_respect_id, apply inverse,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x ∘ _)), apply iso_of_id,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply id_left,
    apply concat, apply (ap (λ x, _ ∘ x)), apply compose_inverse,
    apply id_left,
  end

  check dbl_gpd
  protected definition dbl_gpd : dbl_gpd P lambda_morphism :=
  begin
    fapply dbl_gpd.mk,
      intros, apply (lambda_morphism_comp₁ a_1 a_2),
      intros, apply (lambda_morphism.ID₁ f),
      intros,
  end

  end
end lambda
