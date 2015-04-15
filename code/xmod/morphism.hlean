import .decl algebra.precategory.functor types.pi

open xmod Xmod category path_algebra functor function eq is_trunc pi prod is_equiv equiv
open sigma sigma.ops

namespace xmod

  context
  parameters (X Y : Xmod)
  include X Y

  structure xmod_morphism : Type :=
    (gpd_functor : functor (Groupoid.mk X (gpd X)) (Groupoid.mk Y (gpd Y)))
    (hom_family : Π (p : X), (groups X p) → (groups Y (gpd_functor p)))
    (hom_family_hom : Π (p : X) (x y : groups X p),
      hom_family p (x * y) = hom_family p x * hom_family p y)
    (mu_commute : Π (p : X) (x : groups X p), gpd_functor (μ X x) = μ Y (hom_family p x))
    (phi_commute : Π (p q : X) (a : hom p q) (x : groups X p),
      hom_family q (φ X a x) = φ Y (gpd_functor a) (hom_family p x))

  definition xmod_morphism_hom_family_id (f : xmod_morphism) (p : X) :
    xmod_morphism.hom_family f p 1 = 1 :=
  begin
    assert H : (xmod_morphism.hom_family f p 1) * (xmod_morphism.hom_family f p 1)
      = (xmod_morphism.hom_family f p 1) * 1,
      apply concat, apply inverse, apply xmod_morphism.hom_family_hom,
      apply concat, apply (ap (λ x, xmod_morphism.hom_family f p x)),
        apply one_mul,
      apply inverse, apply mul_one,
    apply (mul_left_cancel H),
  end

  definition xmod_morphism_sigma_char :
    (Σ (gpd_functor : functor (Groupoid.mk X (gpd X)) (Groupoid.mk Y (gpd Y)))
      (hom_family : Π (p : X), (groups X p) → (groups Y (gpd_functor p))),
      (Π (p : X) (x y : groups X p),
        hom_family p (x * y) = (hom_family p x) * (hom_family p y))
      × (Π (p : X) (x : groups X p),
      to_fun_hom gpd_functor (μ X x) = μ Y (hom_family p x))
      × (Π (p q : X) (a : @hom X _ p q) (x : groups X p),
      hom_family q (φ X a x) = φ Y (gpd_functor a) (hom_family p x))) ≃ xmod_morphism :=
  begin
    fapply equiv.mk,
      intro S, cases S with [S1, S'],
      cases S' with [S2, S''],
      cases S'' with [S3, S'''],
      cases S''' with [S4, S5],
      apply (xmod_morphism.mk S1 S2 S3 S4 S5),
    fapply is_equiv.adjointify,
        intro g, cases g with [g1, g2, g3, g4, g5],
        apply (sigma.mk g1), apply (sigma.mk g2), apply ((g3, (g4, g5))),
      intro g, cases g with [g1, g2, g3, g4, g5], apply idp,
    intro S, cases S with [S1, S'],
    cases S' with [S2, S''],
    cases S'' with [S3, S'''],
    cases S''' with [S4, S5],
    apply idp,
  end

  set_option apply.class_instance false
  definition xmod_morphism_hset : is_hset xmod_morphism :=
  begin
    apply is_trunc_equiv_closed,
      apply xmod_morphism_sigma_char,
    apply is_trunc_sigma, intros,
    apply @functor.is_hset_functor, apply (P₀_hset Y),
    intros, apply is_trunc_sigma,
      repeat (apply is_trunc_pi ; intros),
      apply (group.carrier_hset (groups Y (to_fun_ob a a_1))),
    intros, apply is_trunc_prod,
      repeat (apply is_trunc_pi ; intros), apply is_trunc_eq,
      apply is_trunc_succ, apply (group.carrier_hset (groups Y (to_fun_ob a a_2))),
    apply is_trunc_prod,
      repeat (apply is_trunc_pi ; intros), apply is_trunc_eq,
      apply is_trunc_succ, apply homH,
    repeat (apply is_trunc_pi ; intros), apply is_trunc_eq,
    apply is_trunc_succ, apply (group.carrier_hset (groups Y (to_fun_ob a a_3))),
  end

  end

  context
  parameters
    (X Y : Xmod)
    (gpd_functor1 gpd_functor2 : functor (Groupoid.mk X (gpd X)) (Groupoid.mk Y (gpd Y)))
    (hom_family1 : Π (p : X), (groups X p) → (groups Y (gpd_functor1 p)))
    (hom_family_hom1 : Π (p : X) (x y : groups X p),
      hom_family1 p (x * y) = hom_family1 p x * hom_family1 p y)
    (mu_commute1 : Π (p : X) (x : groups X p),
      to_fun_hom gpd_functor1 (μ X x) = μ Y (hom_family1 p x))
    (phi_commute1 : Π (p q : X) (a : hom p q) (x : groups X p),
      hom_family1 q (φ X a x) = φ Y (gpd_functor1 a) (hom_family1 p x))
    (hom_family2 : Π (p : X), (groups X p) → (groups Y (gpd_functor2 p)))
    (hom_family_hom2 : Π (p : X) (x y : groups X p),
      hom_family2 p (x * y) = hom_family2 p x * hom_family2 p y)
    (mu_commute2 : Π (p : X) (x : groups X p),
      to_fun_hom gpd_functor2 (μ X x) = μ Y (hom_family2 p x))
    (phi_commute2 : Π (p q : X) (a : hom p q) (x : groups X p),
      hom_family2 q (φ X a x) = φ Y (gpd_functor2 a) (hom_family2 p x))
    (p : to_fun_ob gpd_functor1 = to_fun_ob gpd_functor2)
    (q : transport (λ x, Π a b, hom a b → hom (x a) (x b)) p
      (to_fun_hom gpd_functor1) = to_fun_hom gpd_functor2)
    (r : transport (λ x, Π p', (groups X p') → (groups Y (x p'))) p hom_family1
         = hom_family2)

  include p q r
  definition xmod_morphism_congr :
    xmod_morphism.mk gpd_functor1 hom_family1 hom_family_hom1 mu_commute1 phi_commute1
    = xmod_morphism.mk gpd_functor2 hom_family2 hom_family_hom2 mu_commute2 phi_commute2 :=
  begin
    cases gpd_functor1 with [gf1, gf2, gf3, gf4],
    cases gpd_functor2 with [gf5, gf6, gf7, gf8],
    cases p, cases q, cases r,
    assert P1 : hom_family_hom1 = hom_family_hom2,
      apply @is_hprop.elim,
      repeat ( apply is_trunc_pi ; intros ),
      apply is_trunc_eq,
    cases P1,
    assert P2 : mu_commute1 = mu_commute2, apply is_hprop.elim,
    cases P2,
    assert P3 : phi_commute1 = phi_commute2,
      apply @is_hprop.elim,
      repeat ( apply is_trunc_pi ; intros ),
      apply is_trunc_eq,
    cases P3,
    assert P4 : gf3 = gf7, apply is_hprop.elim,
    cases P4,
    assert P5 : @gf4 = @gf8, apply is_hprop.elim,
    cases P5,
    apply idp,
  end

  end

  context
  parameters
    {X Y Z : Xmod}
    (g : xmod_morphism Y Z) (f : xmod_morphism X Y)

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

  definition xmod_morphism_id [reducible] (X : Xmod) : xmod_morphism X X :=
  begin
    fapply xmod_morphism.mk,
      apply functor.id,
      intros, apply a,
      intros, apply idp,
      intros, apply idp,
    intros, apply idp,
  end

  context
  parameters
    (X Y Z W : Xmod)
    (h : xmod_morphism Z W) (g : xmod_morphism Y Z) (f : xmod_morphism X Y)

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

  definition xmod_morphism_id_left :
    xmod_morphism_comp (xmod_morphism_id Y) f = f :=
  begin
    cases f,
    fapply xmod_morphism_congr,
        apply idp,
      apply idp,
    repeat (apply eq_of_homotopy ; intros),
    apply idp,
  end

  definition xmod_morphism_id_right :
    xmod_morphism_comp f (xmod_morphism_id X) = f :=
  begin
    cases f,
    fapply xmod_morphism_congr,
        apply idp,
      apply idp,
    repeat (apply eq_of_homotopy ; intros),
    apply idp,
  end

  end

end xmod
