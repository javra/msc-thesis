import ..dbl_gpd.decl ..xmod.decl
set_option apply.class_instance false -- turn off class instance resolution by apply tactic
set_option pp.beta true

open eq sigma is_trunc unit precategory morphism path_algebra xmod groupoid
open equiv sigma.ops



namespace lambda
  context
  parameters {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} [MM : xmod M]
  include P MM

  set_option class.trace_instances true
  abbreviation μ' := (@μ P₀ P M MM)
  abbreviation φ' := (@φ P₀ P M MM)

  structure lambda_morphism ⦃a b c d : P₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d) :=
  (m : M d) (comm : μ' m = i ∘ f ∘ h⁻¹ ∘ g⁻¹)

  definition lambda_morphism.sigma_char ⦃a b c d : P₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d) :
    (Σ (m : M d), μ' m = i ∘ f ∘ h⁻¹ ∘ g⁻¹) ≃ (lambda_morphism f g h i) :=
  begin
    fapply equiv.mk,
      intro S, apply (lambda_morphism.mk S.1 S.2),
    fapply is_equiv.adjointify,
        intro u, apply (lambda_morphism.rec_on u), intros (mu, commu),
        apply (sigma.mk mu commu),
      intro u, apply (lambda_morphism.rec_on u), intros (mu, commu),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (mu, commu),
    apply idp,
  end

  definition lambda_morphism.is_hset ⦃a b c d : P₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d) :
    is_hset (lambda_morphism f g h i) :=
  begin
    apply is_trunc_is_equiv_closed, apply equiv.to_is_equiv, apply lambda_morphism.sigma_char,
    apply is_trunc_sigma, apply group.carrier_hset, apply Group.struct,
    intros, apply is_trunc_succ, apply is_trunc_eq, apply !homH,
  end

  definition lambda_morphism.congr ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {m1 m2 : M d} (comm1 : μ' m1 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (comm2 : μ' m2 = i ∘ f ∘ h⁻¹ ∘ g⁻¹)
    (p1 : m1 = m2) (p2 :
      transport (λ x, μ' x = i ∘ f ∘ h⁻¹ ∘ g⁻¹) p1 comm1 = comm2) :
    (lambda_morphism.mk m1 comm1) = (lambda_morphism.mk m2 comm2) :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1), apply idp,
  end
  definition lambda_morphism.congr' ⦃a b c d : P₀⦄
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
    (p2 : pi ▹ ph ▹ p1 ▹ comm1 = comm2) :
    transport (λ x, lambda_morphism f g h x) pi
      (transport (λ x, lambda_morphism f g x i') ph (lambda_morphism.mk m1 comm1))
    = lambda_morphism.mk m2 comm2 :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1),
    apply (eq.rec_on ph), apply (eq.rec_on pi),
    apply idp,
  end

  definition lambda_morphism.congr_transports' ⦃a b c d : P₀⦄
    {f f' : hom a b} {g g' : hom c d} {h : hom a c} {i : hom b d}
    (pf : f' = f) (pg : g' = g)
    {m1 m2 : M d} (comm1 : μ' m1 = i ∘ f' ∘ h⁻¹ ∘ g'⁻¹)
    (comm2 : μ' m2 = i ∘ f ∘ h⁻¹ ∘ g⁻¹) (p1 : m1 = m2)
    (p2 : pg ▹ pf ▹ p1 ▹ comm1 = comm2) :
    transport (λ x, lambda_morphism f x h i) pg
      (transport (λ x, lambda_morphism x g' h i) pf (lambda_morphism.mk m1 comm1))
    = lambda_morphism.mk m2 comm2 :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1),
    apply (eq.rec_on pf), apply (eq.rec_on pg),
    apply idp,
  end

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
    apply inverse, apply iso.con_inv,
  end

  protected definition lambda_morphism.comp₂ ⦃a b₁ c d₁ b₂ d₂ : P₀⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h₁ : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : lambda_morphism f₂ g₂ i₁ i₂) (u : lambda_morphism f₁ g₁ h₁ i₁) :
    lambda_morphism (f₂ ∘ f₁) (g₂ ∘ g₁) h₁ i₂ :=
  begin
    fapply lambda_morphism.mk,
      exact ((lambda_morphism.m v) * φ g₂ (lambda_morphism.m u)),
    apply concat, apply μ_respect_comp,
    apply concat, apply (ap (λ x, x ∘ _)), apply (lambda_morphism.comm v),
    apply concat, apply (ap (λ x, _ ∘ x)), apply CM1,
    apply concat, apply (ap (λ x, _ ∘ (_ ∘ x ∘ _))), apply (lambda_morphism.comm u),
    apply concat, apply (!assoc⁻¹), apply (ap (λ x, comp i₂ x)),
    apply concat, apply assoc,
    apply concat, apply (ap (λ x, x ∘ _)), apply (!assoc⁻¹),
    apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply (!assoc⁻¹),
    apply concat, apply (ap (λ x, (_ ∘ _ ∘ x) ∘ _)), apply inverse_compose,
    apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply id_right,
    apply concat, apply (ap (λ x, _ ∘ x)), apply (!assoc⁻¹),
    apply concat, apply assoc,
    apply concat, apply (ap (λ x, x ∘ _)), apply (!assoc⁻¹),
    apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply inverse_compose,
    apply concat, apply (ap (λ x, x ∘ _)), apply id_right,
    apply inverse, apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply iso.con_inv,
      apply all_iso, apply all_iso,
    apply concat, apply (!assoc⁻¹),
    apply inverse, apply concat, apply (ap (λ x, _ ∘ x)), apply (!assoc⁻¹),
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply (!assoc⁻¹),
    apply idp,
  end

  protected definition lambda_morphism.ID₁ ⦃a b : P₀⦄ (f : hom a b) :
    lambda_morphism f f id id :=
  begin
    fapply lambda_morphism.mk,
      apply 1,
    apply concat, apply μ_respect_id, apply inverse,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x ∘ _)), apply id_inverse,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply id_left,
    apply concat, apply (ap (λ x, _ ∘ x)), apply compose_inverse,
    apply id_left,
  end

  protected definition lambda_morphism.ID₂ ⦃a b : P₀⦄ (f : hom a b) :
    lambda_morphism id id f f :=
  begin
    fapply lambda_morphism.mk,
      apply 1,
    apply concat, apply μ_respect_id, apply inverse,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ _ ∘ x)), apply id_inverse,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply id_right,
    apply concat, apply (ap (λ x, _ ∘ x)), apply id_left,
    apply compose_inverse,
  end

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
    fapply lambda_morphism.congr_transports,
      apply inverse, apply concat, apply (!mul_assoc⁻¹),
      apply concat, apply (ap (λ x, (x * _) * _)), apply φ_respect_P_comp,
      apply (ap (λ x, x * _)), apply inverse, apply φ_respect_M_comp,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.assoc₂ ⦃a b₁ c d₁ b₂ d₂ b₃ d₃ : P₀⦄
    {f₁ : hom a b₁} {g₁ : hom c d₁} {h : hom a c} {i₁ : hom b₁ d₁}
    {f₂ : hom b₁ b₂} {g₂ : hom d₁ d₂} {i₂ : hom b₂ d₂}
    {f₃ : hom b₂ b₃} {g₃ : hom d₂ d₃} {i₃ : hom b₃ d₃}
    (w : lambda_morphism f₃ g₃ i₂ i₃)
    (v : lambda_morphism f₂ g₂ i₁ i₂)
    (u : lambda_morphism f₁ g₁ h i₁) :
    assoc g₃ g₂ g₁ ▹ assoc f₃ f₂ f₁ ▹
    lambda_morphism.comp₂ w (lambda_morphism.comp₂ v u)
    = lambda_morphism.comp₂ (lambda_morphism.comp₂ w v) u :=
  begin
    fapply lambda_morphism.congr_transports',
      apply inverse, apply concat, apply mul_assoc,
      apply concat, apply (ap (λ x, _ * (_ * x))), apply φ_respect_P_comp,
      apply (ap (λ x, _ * x)), apply inverse, apply φ_respect_M_comp,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_left₁ ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : lambda_morphism f g h i) :
    id_left i ▹ id_left h ▹ lambda_morphism.comp₁ (lambda_morphism.ID₁ g) u = u :=
  begin
    apply (lambda_morphism.rec_on u), intros (mu, commu),
    fapply lambda_morphism.congr_transports,
      apply concat, apply (ap (λ x, x * _)), apply φ_respect_id,
      apply mul_one,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_left₂ ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : lambda_morphism f g h i) :
    id_left g ▹ id_left f ▹ lambda_morphism.comp₂ (lambda_morphism.ID₂ i) u = u :=
  begin
    apply (lambda_morphism.rec_on u), intros (mu, commu),
    fapply lambda_morphism.congr_transports',
      apply concat, apply (ap (λ x, _ * x)), apply φ_respect_id,
      apply one_mul,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_right₁ ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : lambda_morphism f g h i) :
    id_right i ▹ id_right h ▹ lambda_morphism.comp₁ u (lambda_morphism.ID₁ f) = u :=
  begin
    apply (lambda_morphism.rec_on u), intros (mu, commu),
    fapply lambda_morphism.congr_transports,
      apply concat, apply (ap (λ x, x * _)), apply φ_respect_one,
      apply one_mul,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_right₂ ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : lambda_morphism f g h i) :
    id_right g ▹ id_right f ▹ lambda_morphism.comp₂ u (lambda_morphism.ID₂ h) = u :=
  begin
    apply (lambda_morphism.rec_on u), intros (mu, commu),
    fapply lambda_morphism.congr_transports',
      apply concat, apply (ap (λ x, _ * x)), apply φ_respect_one,
      apply mul_one,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_comp₁ ⦃a b c : P₀⦄
    {f : hom a b} {g : hom b c} :
    lambda_morphism.ID₂ (g ∘ f)
    = lambda_morphism.comp₁ (lambda_morphism.ID₂ g) (lambda_morphism.ID₂ f) :=
  begin
    fapply lambda_morphism.congr,
      apply inverse, apply concat, apply (ap (λ x, x * _)), apply φ_respect_one,
      apply one_mul,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.id_comp₂ ⦃a b c : P₀⦄
    {f : hom a b} {g : hom b c} :
    lambda_morphism.ID₁ (g ∘ f)
    = lambda_morphism.comp₂ (lambda_morphism.ID₁ g) (lambda_morphism.ID₁ f) :=
  begin
    fapply lambda_morphism.congr,
      apply inverse, apply concat, apply (ap (λ x, _ * x)), apply φ_respect_one,
      apply one_mul,
    apply is_hset.elim,
  end

  protected definition lambda_morphism.zero_unique ⦃a : P₀⦄ :
    lambda_morphism.ID₁ (ID a) = lambda_morphism.ID₂ (ID a) :=
  begin
    fapply lambda_morphism.congr, apply idp,
    apply is_hset.elim,
  end

  context
  parameters ⦃a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : P₀⦄
    {f₀₀ : hom a₀₀ a₀₁} {f₀₁ : hom a₀₁ a₀₂} {f₁₀ : hom a₁₀ a₁₁}
    {f₁₁ : hom a₁₁ a₁₂} {f₂₀ : hom a₂₀ a₂₁} {f₂₁ : hom a₂₁ a₂₂}
    {g₀₀ : hom a₀₀ a₁₀} {g₀₁ : hom a₀₁ a₁₁} {g₀₂ : hom a₀₂ a₁₂}
    {g₁₀ : hom a₁₀ a₂₀} {g₁₁ : hom a₁₁ a₂₁} {g₁₂ : hom a₁₂ a₂₂}

  protected definition lambda_morphism.interchange
    (x : lambda_morphism f₁₁ f₂₁ g₁₁ g₁₂)
    (w : lambda_morphism f₁₀ f₂₀ g₁₀ g₁₁)
    (v : lambda_morphism f₀₁ f₁₁ g₀₁ g₀₂)
    (u : lambda_morphism f₀₀ f₁₀ g₀₀ g₀₁) :
    lambda_morphism.comp₁ (lambda_morphism.comp₂ x w) (lambda_morphism.comp₂ v u)
    = lambda_morphism.comp₂ (lambda_morphism.comp₁ x v) (lambda_morphism.comp₁ w u) :=
  begin
    fapply lambda_morphism.congr,
      unfold lambda.lambda_morphism.comp₂, esimp,
      unfold lambda.lambda_morphism.comp₁, esimp,
      apply concat, apply (ap (λ x, x * _)), apply φ_respect_M_comp,
      apply inverse, apply concat, apply (ap (λ x, _ * x)), apply φ_respect_M_comp,
      apply concat, apply mul_assoc,
      apply inverse, apply concat, apply mul_assoc,
      apply (ap (λ x, φ g₁₂ (lambda_morphism.m v) * x)),
      apply concat, apply (!mul_assoc⁻¹),
      apply inverse, apply concat,  apply (!mul_assoc⁻¹),
      apply (ap (λ x, x * φ f₂₁ (lambda_morphism.m w))),
      apply eq_mul_of_mul_inv_eq,
      apply concat, apply mul_assoc,
      apply concat, apply inverse, apply (@CM2 P₀ P M MM _ _ _),
      apply concat, apply (ap (λ x, φ x _)), apply (lambda_morphism.comm x),
      apply concat, apply inverse, apply φ_respect_P_comp,
      apply concat, apply inverse, apply φ_respect_P_comp,
      apply inverse, apply concat, apply inverse, apply φ_respect_P_comp, apply inverse,
      apply (ap (λ x, φ x _)),
      apply concat, apply (ap (λ x, (x ∘ _) ∘ _)), apply assoc,
      apply concat, apply (ap (λ x, x ∘ _)), apply (!assoc⁻¹),
      apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply (!assoc⁻¹),
      apply concat, apply (ap (λ x, (_ ∘ _ ∘ x) ∘ _)), apply inverse_compose,
      apply concat, apply (ap (λ x, (_ ∘ x) ∘ _)), apply id_right,
      apply concat, apply (!assoc⁻¹),
      apply concat, apply (ap (λ x, _ ∘ x)), apply inverse_compose,
      apply id_right,
    apply is_hset.elim,
  end

  end

  set_option apply.class_instance true
  protected definition lambda_morphism.inv₁ {a b c d : P₀}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (u : lambda_morphism f g h i) :
    lambda_morphism g f (h⁻¹) (i⁻¹) :=
  begin
    assert (muinv : Group.carrier (M d)),
      apply (has_inv.inv (lambda_morphism.m u)),
    assert (mm : Group.carrier (M b)),
      apply (φ' (i⁻¹) muinv),
    fapply lambda_morphism.mk,
      apply (φ' (i⁻¹) ((lambda_morphism.m u)⁻¹)),
    apply concat, apply CM1,--apply (CM1 (i⁻¹) ((lambda_morphism.m u)⁻¹)),
    apply concat, apply (ap (λ x, _ ∘ x ∘ _)),
      apply (@μ_respect_inv P₀ P M MM d (lambda_morphism.m u)),
    apply concat, apply (ap (λ x, _ ∘ x ∘ _)), apply (ap (λ x, morphism.inverse x)),
      apply (lambda_morphism.comm u),
    apply concat, apply (ap (λ x, _ ∘ x ∘ _)), apply morphism.iso.con_inv,
    --TODO create similar self contained examples for rewriting
    --rewrite [{(i ∘ f ∘ h⁻¹ ∘ g⁻¹)⁻¹}(@morphism.iso.con_inv _ _ _ _ _ i (f ∘ (h⁻¹) ∘ (g⁻¹)) (!all_iso) (!all_iso) (!all_iso))],
    apply concat, apply (ap (λ x, _ ∘ x)), apply inverse, apply assoc,
    apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply compose_inverse,
    apply concat, apply (ap (λ x, _ ∘ x)), apply id_right,
    apply concat, apply (ap (λ x, _ ∘ x)), apply morphism.iso.con_inv,
    apply concat, apply (ap (λ x, _ ∘ x ∘ _)), apply morphism.iso.con_inv,
    apply concat, apply (ap (λ x, _ ∘ x)), apply inverse, apply assoc,
    apply (ap (λ x, _ ∘ x ∘ _)), apply morphism.inverse_involutive,
  end

  protected definition dbl_gpd : dbl_gpd P lambda_morphism :=
  begin
    fapply dbl_gpd.mk,
      intros, apply (lambda_morphism.comp₁ a_1 a_2),
      intros, apply (lambda_morphism.ID₁ f),
      intros, apply lambda_morphism.assoc₁,
      intros, apply lambda_morphism.id_left₁,
      intros, apply lambda_morphism.id_right₁,
      intros, apply lambda_morphism.is_hset,
      intros, apply (lambda_morphism.comp₂ a_1 a_2),
      intros, apply (lambda_morphism.ID₂ f),
      intros, apply lambda_morphism.assoc₂,
      intros, apply lambda_morphism.id_left₂,
      intros, apply lambda_morphism.id_right₂,
      intros, apply lambda_morphism.is_hset,
      intros, apply lambda_morphism.id_comp₁,
      intros, apply lambda_morphism.id_comp₂,
      intros, apply lambda_morphism.zero_unique,
      intros, apply lambda_morphism.interchange,
      intros, apply lambda_morphism.inv₁,
  end

  end
end lambda
