import .decl .basic

open dbl_precat category is_trunc eq

namespace dbl_precat
  section
  parameters {D₀ : Type} [D₀set : is_hset D₀] [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type}
    [D : dbl_precat C D₂]
  include D D₀set C

  section
  variables {a b c d b₂ d₂ : D₀} {E : Type}
    {f : hom a b} {g : hom c d} {h : hom a c} {i : hom b d}
    {f₂ : hom b b₂} {g₂ : hom d d₂} {i₂ : hom b₂ d₂}

  definition transp_comp₂_eq_comp₂_transp_l_bu {y z w : D₀}
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id)
    (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ (f' ∘ (ef x)) _ id id) p
      (transport (λ x, D₂ _ (g' ∘ (eg x)) id id) q
        (comp₂ D filler' filler))
    = comp₂ D filler'
        (transport (λ x, D₂ (ef x) _ id id) p
          (transport (λ x, D₂ _ (eg x) id id) q filler)) :=
  by cases q; cases p; apply idp

  definition transp_comp₂_eq_comp₂_transp_l_b {y z w : D₀}
    {eg : E → hom z y} {f1 : hom z y}
    {g1 g2 : E} (filler : D₂ f1 (eg g1) id id) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ (g' ∘ (eg x)) id id) q
        (comp₂ D filler' filler)
    = comp₂ D filler'
        (transport (λ x, D₂ _ (eg x) id id) q filler) :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_l_l {e : E → hom a c}
    {h h' : E} (q : h = h')
    (u : D₂ f g (e h) i) (v : D₂ f₂ g₂ i i₂) :
    transport (λ x, D₂ _ _ (e x) _) q (comp₂ D v u)
    = comp₂ D v (transport (λ x, D₂ _ _ (e x) _) q u) :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_l_u' {e : E → hom a b}
    {f f' : E} (q : f = f')
    (u : D₂ (e f) g h i) (v : D₂ f₂ g₂ i i₂) :
    transport (λ x, D₂ (f₂ ∘ (e x)) _ _ _) q (comp₂ D v u)
    = comp₂ D v (transport (λ x, D₂ (e x) _ _ _) q u) :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_l_b' {e : E → hom c d}
    {g g' : E} (q : g = g')
    (u : D₂ f (e g) h i) (v : D₂ f₂ g₂ i i₂) :
    transport (λ x, D₂ _ (g₂ ∘ (e x)) _ _) q (comp₂ D v u)
    = comp₂ D v (transport (λ x, D₂ _ (e x) _ _) q u) :=
  begin
    apply (eq.rec_on q), apply idp,
  end

  definition transp_comp₂_eq_comp₂_transp_r_u' {e : E → hom b b₂}
    {f₂ f₂' : E} (q : f₂ = f₂')
    (u : D₂ f g h i) (v : D₂ (e f₂) g₂ i i₂) :
    transport (λ x, D₂ ((e x) ∘ f) _ _ _) q (comp₂ D v u)
    = comp₂ D (transport (λ x, D₂ (e x) _ _ _) q v) u :=
  by cases q; apply idp

  definition transp_comp₂_inner_deal1 {e : E → hom b d}
    {i i' : E} (q : i = i')
    (u : D₂ f g h (e i)) (v : D₂ f₂ g₂ (e i') i₂) :
    comp₂ D v (transport (λ x, D₂ _ _ _ (e x)) q u)
    = comp₂ D (transport (λ x, D₂ _ _ (e x) _) q⁻¹ v) u :=
  by cases q; apply idp

  definition transp_comp₂_inner_deal2 {e : E → hom b d}
    {i i' : E} (q : i = i')
    (u : D₂ f g h (e i')) (v : D₂ f₂ g₂ (e i) i₂) :
    comp₂ D (transport (λ x, D₂ _ _ (e x) _) q v) u
    = comp₂ D v (transport (λ x, D₂ _ _ _ (e x)) q⁻¹ u) :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_r_b' {e : E → hom d d₂}
    {g₂ g₂' : E} (q: g₂ = g₂')
    (u : D₂ f g h i) (v : D₂ f₂ (e g₂) i i₂) :
    transport (λ x, D₂ _ ((e x) ∘ g) _ _) q (comp₂ D v u)
    = comp₂ D (transport (λ x, D₂ _ (e x) _ _) q v) u :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_r_r {e : E → hom b₂ d₂}
    {i₂ i₂' : E}  (q : i₂ = i₂')
    (u : D₂ f g h i) (v : D₂ f₂ g₂ i (e i₂)) :
    transport (λ x, D₂ _ _ _ (e x)) q (comp₂ D v u)
    = comp₂ D (transport (λ x, D₂ _ _ _ (e x)) q v) u :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_inner {e : E → hom b d}
    {i i' : E} (q : i = i')
    (u : D₂ f g h (e i)) (v : D₂ f₂ g₂ (e i) i₂) :
    comp₂ D v u = comp₂ D (transport (λ x, D₂ _ _ (e x) _) q v)
      (transport (λ x, D₂ _ _ _ (e x)) q u) :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_r_b {y z w : D₀}
    {Eg : Type} {eg : Eg → hom y w} {f1 : hom y w}
    {g1 g2 : Eg} (filler : D₂ f1 (eg g1) id id) (q : g1 = g2)
    {f' g' : hom z y} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ ((eg x) ∘ g') id id) q (comp₂ D filler filler')
    = comp₂ D (transport (λ x, D₂ _ (eg x) id id) q filler) filler' :=
  by cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_r_bu {y z w : D₀}
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ ((ef x) ∘ f') _ id id) p
      (transport (λ x, D₂ _ ((eg x) ∘ g') id id) q
        (comp₂ D filler filler'))
    = comp₂ D (transport (λ x, D₂ (ef x) _ id id) p
          (transport (λ x, D₂ _ (eg x) id id) q filler)) filler' :=
  by cases q; cases p; apply idp

  definition transp_comp₂_eq_comp₂_transp_l_ub {y z w : D₀}
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ (g' ∘ (eg x)) id id) q
      (transport (λ x, D₂ (f' ∘ (ef x)) _ id id) p
        (comp₂ D filler' filler))
    = comp₂ D filler'
       (transport (λ x, D₂ _ (eg x) id id) q
         (transport (λ x, D₂ (ef x) _ id id) p filler)) :=
  by cases p; cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_r_ub {y z w : D₀}
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ ((eg x) ∘ g') id id) q
      (transport (λ x, D₂ ((ef x) ∘ f') _ id id) p
        (comp₂ D filler filler'))
    = comp₂ D (transport (λ x, D₂ _ (eg x) id id) q
          (transport (λ x, D₂ (ef x) _ id id) p filler)) filler' :=
  by cases p; cases q; apply idp

  definition transp_comp₂_eq_comp₂_transp_transp_rl {a b₁ b₂ c d₁ d₂ : D₀}
    {Eh₁ Ei₁ Ei₂ : Type} {eh₁ : Eh₁ → hom a c} {ei₁ : Ei₁ → hom b₁ d₁}
    {ei₂ : Ei₂ → hom b₂ d₂} [Ei₁_hset : is_hset Ei₁]
    {f₁ : hom a b₁} {g₁ : hom c d₁} {h₁ h₁' : Eh₁} {i₁ i₁' : Ei₁}
    {f₂ : hom b₁ b₂} {g₂ : hom d₁ d₂} {i₂ i₂' : Ei₂}
    (ph₁ : h₁ = h₁') (pi₁ pi₁' : i₁ = i₁') (pi₂ : i₂ = i₂')
    (v : D₂ f₂ g₂ (ei₁ i₁) (ei₂ i₂)) (u : D₂ f₁ g₁ (eh₁ h₁) (ei₁ i₁)) :
    transport (λ x, D₂ _ _ (eh₁ x) _) ph₁
      (transport (λ x, D₂ _ _ _ (ei₂ x)) pi₂
        (comp₂ D v u))
    = comp₂ D
        (transport (λ x, D₂ _ _ (ei₁ x) _) pi₁
          (transport (λ x, D₂ _ _ _ (ei₂ x)) pi₂ v))
        (transport (λ x, D₂ _ _ (eh₁ x) _) ph₁
          (transport (λ x, D₂ _ _ _ (ei₁ x)) pi₁' u)) :=
  begin
    cases ph₁, cases pi₂,
    assert H : pi₁ = pi₁', apply @is_hset.elim,
    cases H, cases pi₁, apply idp,
  end

  end

  section
  variables {a b c₁ d₁ c₂ d₂ : D₀} {E : Type} {e : E → hom c₁ d₁}
    {f₁ : hom a b} {g₁ : hom c₁ d₁} {h₁ : hom a c₁} {i₁ : hom b d₁}
    {g₂ : hom c₂ d₂} {h₂ : hom c₁ c₂} {i₂ : hom d₁ d₂}

  definition comp₁_transp_eq_comp₁_transp_b {e : E → hom c₁ d₁}
    {g₁ g₁' : E} (pg₁ : g₁ = g₁')
    (v : D₂ (e g₁') g₂ h₂ i₂) (u : D₂ f₁ (e g₁) h₁ i₁) :
    comp₁ D (transport (λ x, D₂ (e x) g₂ h₂ i₂) (pg₁⁻¹) v) u = comp₁ D v (pg₁ ▹ u) :=
  by cases pg₁; apply idp

  definition transp_comp₁_eq_comp₁_transp_b_b {e : E → hom c₂ d₂}
    {g₂ g₂' : E} (pg₁ : g₂ = g₂')
    (v : D₂ g₁ (e g₂) h₂ i₂) (u : D₂ f₁ g₁ h₁ i₁) :
    transport (λ x, D₂ _ (e x) _ _) pg₁ (comp₁ D v u)
    = comp₁ D (transport (λ x, D₂ _ (e x) _ _) pg₁ v) u :=
  by cases pg₁; apply idp

  definition transp_comp₁_eq_comp₁_transp_u_rl {y z w : D₀}
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id (f' ∘ (ef x)) _) p
      (transport (λ x, D₂ id id _ (g' ∘ (eg x))) q
        (comp₁ D filler' filler))
    = comp₁ D filler'
        (transport (λ x, D₂ id id (ef x) _) p
          (transport (λ x, D₂ id id _ (eg x)) q filler)) :=
  by cases q; cases p; apply idp

  definition transp_comp₁_eq_comp₁_transp_u_r {e : E → hom b d₁}
    {i₁ i₁' : E} (p : i₁ = i₁')
    (v : D₂ g₁ g₂ h₂ i₂) (u : D₂ f₁ g₁ h₁ (e i₁)) :
    transport (λ x, D₂ _ _ _ (i₂ ∘ (e x))) p (comp₁ D v u)
    = comp₁ D v (transport (λ x, D₂ _ _ _ (e x)) p u) :=
  by cases p; apply idp

  definition transp_comp₁_eq_comp₁_transp_u_l {e : E → hom a c₁}
    {h₁ h₁' : E} (p : h₁ = h₁')
    (v : D₂ g₁ g₂ h₂ i₂) (u : D₂ f₁ g₁ (e h₁) i₁) :
    transport (λ x, D₂ _ _ (h₂ ∘ (e x)) _) p (comp₁ D v u)
    = comp₁ D v (transport (λ x, D₂ _ _ (e x) _) p u) :=
  by cases p; apply idp

  definition transp_comp₁_eq_comp₁_transp_b_rl {y z w : D₀}
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id ((ef x) ∘ f') _) p
      (transport (λ x, D₂ id id _ ((eg x) ∘ g')) q
        (comp₁ D filler filler'))
    = comp₁ D (transport (λ x, D₂ id id (ef x) _) p
          (transport (λ x, D₂ id id _ (eg x)) q filler)) filler' :=
  by cases q; cases p; apply idp

  definition transp_comp₁_eq_comp₁_transp_u_lr {y z w : D₀}
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id _ (g' ∘ (eg x))) q
      (transport (λ x, D₂ id id (f' ∘ (ef x)) _) p
        (comp₁ D filler' filler))
    = comp₁ D filler'
       (transport (λ x, D₂ id id _ (eg x)) q
         (transport (λ x, D₂ id id (ef x) _) p filler)) :=
  by cases p; cases q; apply idp

  definition transp_comp₁_eq_comp₁_transp_b_lr {y z w : D₀}
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id _ ((eg x) ∘ g')) q
      (transport (λ x, D₂ id id ((ef x) ∘ f') _) p
        (comp₁ D filler filler'))
    = comp₁ D (transport (λ x, D₂ id id _ (eg x)) q
          (transport (λ x, D₂ id id (ef x) _) p filler)) filler' :=
  by cases p; cases q; apply idp

  end

  end
end dbl_precat
