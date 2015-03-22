import .lambda algebra.precategory.functor
import ..xmod.category_of ..dbl_gpd.category_of

open eq category iso is_trunc path_algebra function xmod Xmod dbl_gpd functor

namespace lambda

  protected definition functor_on_hom_aux1 {P₀ : Type} [P : groupoid P₀]
    {M : P₀ → Group} [MM : xmod M] ⦃a b c d : P₀⦄
    {f f' : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    (M : lambda_morphism f g h i) (p : f = f') :
    lambda_morphism.m (p ▹ M) = lambda_morphism.m M :=
  begin
    cases p, apply idp,
  end

  protected definition functor_on_hom_aux2 {P₀ : Type} [P : groupoid P₀]
    {M : P₀ → Group} [MM : xmod M] ⦃a b c d : P₀⦄
    {f : hom a b} {g g' : hom c d} {h : hom a c} {i : hom b d}
    (M : lambda_morphism f g h i) (p : g = g') :
    lambda_morphism.m (p ▹ M) = lambda_morphism.m M :=
  begin
    cases p, apply idp,
  end

  protected definition functor_on_hom_aux3 {P₀ : Type} [P : groupoid P₀]
    {M : P₀ → Group} [MM : xmod M] ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h h' : hom a c} {i : hom b d}
    (M : lambda_morphism f g h i) (p : h = h') :
    lambda_morphism.m (p ▹ M) = lambda_morphism.m M :=
  begin
    cases p, apply idp,
  end

  protected definition functor_on_hom_aux4 {P₀ : Type} [P : groupoid P₀]
    {M : P₀ → Group} [MM : xmod M] ⦃a b c d : P₀⦄
    {f : hom a b} {g : hom c d} {h : hom a c} {i i' : hom b d}
    (M : lambda_morphism f g h i) (p : i = i') :
    lambda_morphism.m (p ▹ M) = lambda_morphism.m M :=
  begin
    cases p, apply idp,
  end

  protected definition on_morphisms {X Y : Xmod} (f : xmod_morphism X Y) :
    (dbl_functor (lambda.on_objects X) (lambda.on_objects Y)) :=
  begin
    cases f with (F, ψ, f3, f4, f5),
    fapply dbl_functor.mk, exact F,
      intros (a, b, c, d, f, g, h, i),
      esimp{lambda.on_objects, lambda.dbl_gpd}, intro m, cases m with (m1, m2),
      {fapply lambda_morphism.mk, apply (ψ d m1),
        apply concat, apply inverse, apply (f4 d m1),
        apply concat, apply (ap (λ x, to_fun_hom F x)), apply m2,
        apply concat, apply (respect_comp F),
        apply concat, apply (ap (λ x, _ ∘ x)), apply (respect_comp F),
        apply concat, apply (ap (λ x, _ ∘ _ ∘ x)), apply (respect_comp F),
        apply concat, apply (ap (λ x, _ ∘ _ ∘ x ∘ _)),
          apply (@functor.respect_inv _ _ F _ _ h (!all_iso)),
        apply concat, apply (ap (λ x, _ ∘ _ ∘ _ ∘ x)),
          apply (@functor.respect_inv _ _ F _ _ g (!all_iso)),
        apply idp,},
      {intros (p, q, a), fapply lambda_morphism.congr',
        apply concat, apply functor_on_hom_aux4,
        apply concat, apply functor_on_hom_aux3,
        apply (xmod_morphism_hom_family_id X Y (xmod_morphism.mk F ψ f3 f4 f5)),
      apply is_hset.elim,},
      {intros, fapply lambda_morphism.congr',
        apply concat, apply functor_on_hom_aux4,
        apply concat, apply functor_on_hom_aux3,
        apply concat, apply f3,
        cases v, cases u, apply (ap (λ x, x * _)), apply f5,
      apply is_hset.elim,},
      {intros (p, q, a), fapply lambda_morphism.congr',
        apply concat, apply functor_on_hom_aux2,
        apply concat, apply functor_on_hom_aux1,
        apply (xmod_morphism_hom_family_id X Y (xmod_morphism.mk F ψ f3 f4 f5)),
      apply is_hset.elim,},
      {intros, fapply lambda_morphism.congr',
        apply concat, apply functor_on_hom_aux2,
        apply concat, apply functor_on_hom_aux1,
        apply concat, apply f3,
        cases v, cases u, apply (ap (λ x, _ * x)), apply f5,
      apply is_hset.elim,},
  end

end lambda
