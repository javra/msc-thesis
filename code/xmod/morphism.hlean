import .decl algebra.precategory.functor

open xmod category path_algebra functor function eq

namespace xmod

  context
  parameters
    {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} (X : xmod M)
    {Q₀ : Type} [Q : groupoid Q₀] {N : Q₀ → Group} (Y : xmod N)
  include P X Q Y

  definition φX [reducible] := @φ P₀ P M X
  definition φY [reducible] := @φ Q₀ Q N Y

  structure xmod_morphism : Type :=
    (gpd_functor : functor (Groupoid.mk P₀ P) (Groupoid.mk Q₀ Q))
    (hom_family : Π (p : P₀), (M p) → (N (gpd_functor p)))
    (hom_family_hom : Π (p : P₀) (x y : M p),
      hom_family p (x * y) = hom_family p x * hom_family p y)
    (mu_commute : Π (p : P₀) (x : M p),
      to_fun_hom gpd_functor (μ P x) = μ Q (hom_family p x))
    (phi_commute : Π (p q : P₀) (a : @hom P₀ P p q) (x : M p),
      hom_family q (φX a x) = φY (to_fun_hom gpd_functor a) (hom_family p x))

  end

  context
  parameters
    {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} {X : xmod M}
    {Q₀ : Type} [Q : groupoid Q₀] {N : Q₀ → Group} {Y : xmod N}
    {R₀ : Type} [R : groupoid R₀] {O : R₀ → Group} {Z : xmod O}
    (g : xmod_morphism Y Z)
    (f : xmod_morphism X Y)

  include g f
  open xmod_morphism

  definition xmod_morphism_comp [reducible] : xmod_morphism X Z :=
  begin
    fapply xmod_morphism.mk,
      apply (functor.compose (gpd_functor g) (gpd_functor f)),
      intros, apply (hom_family g), apply (hom_family f), apply a,
      intros, apply concat, apply (ap (λ x, hom_family g _ x)),
        apply (hom_family_hom f), apply (hom_family_hom g),
      intros, apply concat, apply (ap (λ x, to_fun_hom (gpd_functor g) x)),
        apply (mu_commute f), apply (mu_commute g),
    intros, apply concat, apply (ap (λ x, hom_family _ _ x)),
      apply (phi_commute f), apply (phi_commute g),
  end

  end

  context
  parameters
    {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} (X : xmod M)

  definition xmod_morphism_id [reducible] : xmod_morphism X X :=
  begin
    fapply xmod_morphism.mk,
      apply functor.id,
      intros, apply a,
      intros, apply idp,
      intros, apply idp,
    intros, apply idp,
  end

  end

end xmod
