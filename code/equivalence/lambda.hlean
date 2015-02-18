import ..dbl_gpd.decl ..xmod.decl
set_option apply.class_instance false -- turn off class instance resolution by apply tactic
set_option pp.beta true

open eq sigma unit precategory morphism path_algebra xmod groupoid

attribute Group.struct [coercion]

namespace lambda
  context
  parameters {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} [MM : xmod M]

  set_option class.trace_instances true
  abbreviation μ' := (@μ P₀ P M MM)

  structure lambda_morphism ⦃a b c d : P₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d) :=
  (m : M d) (comm : μ' m = i ∘ f ∘ h⁻¹ ∘ g⁻¹)

  include P MM

  protected definition lambda_morphism.congr ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {m1 m2 : M d} (comm1 : μ' m1 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (comm2 : μ' m2 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (p1 : m1 = m2) (p2 :
      transport (λ x, μ' x = i ∘ f ∘ h⁻¹ ∘ g⁻¹) p1 comm1 = comm2) :
    (lambda_morphism.mk m1 comm1) = (lambda_morphism.mk m2 comm2) :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1), apply idp,
  end
  protected definition lambda_morphism.congr' ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (v u : lambda_morphism f g h i)
    (p1 : lambda_morphism.m v = lambda_morphism.m u)
    (p2 : p1 ▹ (lambda_morphism.comm v) = (lambda_morphism.comm u)) : v = u :=
  begin
    revert p2, revert p1,
    apply (lambda_morphism.rec_on v), intros (m_v, comm_v),
    apply (lambda_morphism.rec_on u), intros (m_u, comm_u),
    intros (p1, p2), apply lambda_morphism.congr, apply p2,
  end

  definition lambda_morphism.congr_transports ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h h' : hom a c} {i i' : hom b d}
    (ph : h' = h) (pi : i' = i)
    {m1 m2 : M d} (comm1 : μ' m1 = i' ∘ f ∘ h'⁻¹ ∘ g⁻¹)
    (comm2 : μ' m2 = i ∘ f ∘ h⁻¹ ∘ g⁻¹) (p1 : m1 = m2)
    (p2 : (transport (λ x, μ' m2 = x ∘ f ∘ h⁻¹ ∘ g⁻¹) pi
            (transport (λ x, μ' m2 = i' ∘ f ∘ x⁻¹ ∘ g⁻¹) ph
              (transport (λ x, μ' x = i' ∘ f ∘ h'⁻¹ ∘ g⁻¹) p1 comm1))) = comm2) :
    transport (λ x, lambda_morphism f g h x) pi
      (transport (λ x, lambda_morphism f g x i') ph (lambda_morphism.mk m1 comm1))
    = (lambda_morphism.mk m2 comm2) :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1),
    apply (eq.rec_on ph), apply (eq.rec_on pi),
    apply idp,
  end

  end
exit
  protected definition lambda_morphism.comp₁ ⦃a b c₁ d₁ c₂ d₂ : P₀⦄
    ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : lambda_morphism g₁ g₂ h₂ i₂) (u : lambda_morphism f₁ g₁ h₁ i₁) :
    lambda_morphism f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁) :=
  begin
    fapply lambda_morphism.mk,
      exact ((φ i₂ (lambda_morphism.m u)) * (lambda_morphism.m v)),
    apply concat, apply μ_respect_comp,
    apply concat, apply (ap (λ x, _ ∘ x)), apply (lambda_morphism.comm v),
    apply concat, apply (ap (λ x, x ∘ _)), apply CM1,
    apply concat, apply (ap (λ x, (_ ∘ x ∘ _) ∘ _)), apply (lambda_morphism.comm u),
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

  --set_option pp.notation false
  --set_option pp.implicit true
  check @has_mul.mul

  protected definition lambda_morphism.assoc₁ ⦃a b c₁ d₁ c₂ d₂ c₃ d₃ : P₀⦄
    {f : hom a b} {g₁ : hom c₁ d₁} {h₁ : hom a c₁} {i₁ : hom b d₁} {g₂ : hom c₂ d₂}
    {h₂ : hom c₁ c₂} {i₂ : hom d₁ d₂} {g₃ : hom c₃ d₃} {h₃ : hom c₂ c₃} {i₃ : hom d₂ d₃}
    (w : lambda_morphism g₂ g₃ h₃ i₃)
    (v : lambda_morphism g₁ g₂ h₂ i₂)
    (u : lambda_morphism f g₁ h₁ i₁) :
    assoc i₃ i₂ i₁ ▹ assoc h₃ h₂ h₁ ▹
    lambda_morphism.comp₁ w (lambda_morphism.comp₁ v u)
    = lambda_morphism.comp₁ (lambda_morphism.comp₁ w v) u :=
  begin
    /-apply (lambda_morphism.rec_on w), intros (mw, commw),
    apply (lambda_morphism.rec_on v), intros (mv, commv),
    apply (lambda_morphism.rec_on u), intros (mu, commu),-/
    --unfold lambda.lambda_morphism.comp₁,
    fapply lambda_morphism.congr_tranports,
      apply inverse, apply concat, apply (!mul_assoc⁻¹),
      apply concat, apply (ap (λ x, @has_mul.mul _ (Group.struct (M _))
            (@has_mul.mul _ (Group.struct (M _)) x _) _)),
        apply φ_respect_P_comp,
      apply (ap (λ x, x * _)), apply inverse, apply φ_respect_M_comp,
  end

exit
  check dbl_gpd
  protected definition dbl_gpd : dbl_gpd P lambda_morphism :=
  begin
    fapply dbl_gpd.mk,
      intros, apply (lambda_morphism.comp₁ a_1 a_2),
      intros, apply (lambda_morphism.ID₁ f),
      intros,
  end

  end
end lambda

exit

      /-apply inverse,
        unfold lambda.lambda_morphism.m, unfold lambda.lambda_morphism.comp₁, esimp,-/
      /-apply concat,
        unfold lambda.lambda_morphism.m, unfold lambda.lambda_morphism.comp₁, esimp,
        apply (!mul_assoc⁻¹),-/
      /-apply concat, apply (ap (λ x, @has_mul.mul _ (Group.struct (M _))
            (@has_mul.mul _ (Group.struct (M _)) x _) _)),
        apply φ_respect_P_comp,-/
      --apply concat, apply (ap (λ x, x * _)), apply inverse, apply φ_respect_M_comp,
