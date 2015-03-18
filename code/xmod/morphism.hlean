import .decl algebra.precategory.functor types.pi

open xmod category path_algebra functor function eq is_trunc pi

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
      hom_family q (@φ P₀ P M X _ _ a x)
      = @φ Q₀ Q N Y _ _ (to_fun_hom gpd_functor a) (hom_family p x))

  end

  context
  parameters
    {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} (X : xmod M)
    {Q₀ : Type} [Q : groupoid Q₀] {N : Q₀ → Group} (Y : xmod N)
    (gpd_functor1 gpd_functor2 : functor (Groupoid.mk P₀ P) (Groupoid.mk Q₀ Q))
    (hom_family1 : Π (p : P₀), (M p) → (N (gpd_functor1 p)))
    (hom_family2 : Π (p : P₀), (M p) → (N (gpd_functor2 p)))
    (hom_family_hom1 : Π (p : P₀) (x y : M p),
      hom_family1 p (x * y) = hom_family1 p x * hom_family1 p y)
    (hom_family_hom2 : Π (p : P₀) (x y : M p),
      hom_family2 p (x * y) = hom_family2 p x * hom_family2 p y)
    (mu_commute1 : Π (p : P₀) (x : M p),
      to_fun_hom gpd_functor1 (μ P x) = μ Q (hom_family1 p x))
    (mu_commute2 : Π (p : P₀) (x : M p),
      to_fun_hom gpd_functor2 (μ P x) = μ Q (hom_family2 p x))
    (phi_commute1 : Π (p q : P₀) (a : @hom P₀ P p q) (x : M p),
      hom_family1 q (@φ P₀ P M X _ _ a x)
      = @φ Q₀ Q N Y _ _ (to_fun_hom gpd_functor1 a) (hom_family1 p x))
    (phi_commute2 : Π (p q : P₀) (a : @hom P₀ P p q) (x : M p),
      hom_family2 q (@φ P₀ P M X _ _ a x)
      = @φ Q₀ Q N Y _ _ (to_fun_hom gpd_functor2 a) (hom_family2 p x))
    (p : to_fun_ob gpd_functor1 = to_fun_ob gpd_functor2)
    (q : transport (λ x, Π a b, hom a b → hom (x a) (x b)) p
      (to_fun_hom gpd_functor1) = to_fun_hom gpd_functor2)
    (r : transport (λ x, Π p', (M p') → (N (x p'))) p hom_family1 = hom_family2)

  include p q r
  definition xmod_morphism_congr :
    xmod_morphism.mk gpd_functor1 hom_family1 hom_family_hom1 mu_commute1 phi_commute1
    = xmod_morphism.mk gpd_functor2 hom_family2 hom_family_hom2 mu_commute2 phi_commute2 :=
  begin
    cases gpd_functor1 with (gf1, gf2, gf3, gf4),
    cases gpd_functor2 with (gf5, gf6, gf7, gf8),
    cases p, cases q, cases r,
    assert P1 : hom_family_hom1 = hom_family_hom2,
      apply @is_hprop.elim,
      repeat ( apply is_trunc_pi ; intros ),
      apply is_trunc_eq, apply semigroup.carrier_hset,
    cases P1,
    assert P2 : mu_commute1 = mu_commute2,
      apply is_hprop.elim,
    cases P2,
    assert P3 : phi_commute1 = phi_commute2,
      apply @is_hprop.elim,
      repeat ( apply is_trunc_pi ; intros ),
      apply is_trunc_eq, apply semigroup.carrier_hset,
    cases P3,
    assert P4 : gf3 = gf7,
      apply is_hprop.elim,
    cases P4,
    assert P5 : @gf4 = @gf8,
      apply is_hprop.elim,
    cases P5,
    apply idp,
  end

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

  context
  parameters
    {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group} {X : xmod M}
    {Q₀ : Type} [Q : groupoid Q₀] {N : Q₀ → Group} {Y : xmod N}
    {R₀ : Type} [R : groupoid R₀] {O : R₀ → Group} {Z : xmod O}
    {S₀ : Type} [S : groupoid S₀] {T : S₀ → Group} {W : xmod T}
    (h : xmod_morphism Z W)
    (g : xmod_morphism Y Z)
    (f : xmod_morphism X Y)

  definition xmod_morphism_assoc :
    xmod_morphism_comp h (xmod_morphism_comp g f)
    = xmod_morphism_comp (xmod_morphism_comp h g) f :=
  begin
    fapply xmod_morphism_congr,
        apply idp,
      apply idp,
    repeat (apply eq_of_homotopy ; intros),
    apply idp,
  end

  end

end xmod
