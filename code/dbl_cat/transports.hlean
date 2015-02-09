import .decl .basic

open dbl_precat precategory truncation
open morphism eq

namespace dbl_precat
  context
  universe variable l
  parameters {D₀ : Type.{l}}
    [D₀set : is_hset D₀]
    [C : precategory.{l l} D₀]
    {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type.{l}}
    [G : dbl_precat C D₂]
  include G D₀set C


  definition transp_comp₂_eq_comp₂_transp_l_bu ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ (f' ∘ (ef x)) _ id id) p
      (transport (λ x, D₂ _ (g' ∘ (eg x)) id id) q
        (comp₂ D₂ filler' filler))
    = comp₂ D₂ filler'
        (transport (λ x, D₂ (ef x) _ id id) p
          (transport (λ x, D₂ _ (eg x) id id) q filler)) :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  definition transp_comp₂_eq_comp₂_transp_r_bu ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ ((ef x) ∘ f') _ id id) p
      (transport (λ x, D₂ _ ((eg x) ∘ g') id id) q
        (comp₂ D₂ filler filler'))
    = comp₂ D₂ (transport (λ x, D₂ (ef x) _ id id) p
          (transport (λ x, D₂ _ (eg x) id id) q filler)) filler' :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  definition transp_comp₂_eq_comp₂_transp_l_ub ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ (g' ∘ (eg x)) id id) q
      (transport (λ x, D₂ (f' ∘ (ef x)) _ id id) p
        (comp₂ D₂ filler' filler))
    = comp₂ D₂ filler'
       (transport (λ x, D₂ _ (eg x) id id) q
         (transport (λ x, D₂ (ef x) _ id id) p filler)) :=
  begin
    apply (eq.rec_on p), apply (eq.rec_on q), apply idp,
  end

  definition transp_comp₂_eq_comp₂_transp_r_ub ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ (ef f1) (eg g1) id id) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ f' g' id id) :
    transport (λ x, D₂ _ ((eg x) ∘ g') id id) q
      (transport (λ x, D₂ ((ef x) ∘ f') _ id id) p
        (comp₂ D₂ filler filler'))
    = comp₂ D₂ (transport (λ x, D₂ _ (eg x) id id) q
          (transport (λ x, D₂ (ef x) _ id id) p filler)) filler' :=
  begin
    apply (eq.rec_on p), apply (eq.rec_on q), apply idp,
  end

  definition transp_comp₁_eq_comp₁_transp_l_bu ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id (f' ∘ (ef x)) _) p
      (transport (λ x, D₂ id id _ (g' ∘ (eg x))) q
        (comp₁ D₂ filler' filler))
    = comp₁ D₂ filler'
        (transport (λ x, D₂ id id (ef x) _) p
          (transport (λ x, D₂ id id _ (eg x)) q filler)) :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  definition transp_comp₁_eq_comp₁_transp_r_bu ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id ((ef x) ∘ f') _) p
      (transport (λ x, D₂ id id _ ((eg x) ∘ g')) q
        (comp₁ D₂ filler filler'))
    = comp₁ D₂ (transport (λ x, D₂ id id (ef x) _) p
          (transport (λ x, D₂ id id _ (eg x)) q filler)) filler' :=
  begin
    apply (eq.rec_on q), apply (eq.rec_on p), apply idp,
  end

  definition transp_comp₁_eq_comp₁_transp_l_ub ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom z y}
    {Eg : Type} {eg : Eg → hom z y}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom y w} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id _ (g' ∘ (eg x))) q
      (transport (λ x, D₂ id id (f' ∘ (ef x)) _) p
        (comp₁ D₂ filler' filler))
    = comp₁ D₂ filler'
       (transport (λ x, D₂ id id _ (eg x)) q
         (transport (λ x, D₂ id id (ef x) _) p filler)) :=
  begin
    apply (eq.rec_on p), apply (eq.rec_on q), apply idp,
  end

  definition transp_comp₁_eq_comp₁_transp_r_ub ⦃y z w : D₀⦄
    {Ef : Type} {ef : Ef → hom y z}
    {Eg : Type} {eg : Eg → hom y z}
    {f1 f2 : Ef} {g1 g2 : Eg} (filler : D₂ id id (ef f1) (eg g1)) (p : f1 = f2) (q : g1 = g2)
    {f' g' : hom w y} (filler' : D₂ id id f' g') :
    transport (λ x, D₂ id id _ ((eg x) ∘ g')) q
      (transport (λ x, D₂ id id ((ef x) ∘ f') _) p
        (comp₁ D₂ filler filler'))
    = comp₁ D₂ (transport (λ x, D₂ id id _ (eg x)) q
          (transport (λ x, D₂ id id (ef x) _) p filler)) filler' :=
  begin
    apply (eq.rec_on p), apply (eq.rec_on q), apply idp,
  end

  end
end dbl_precat
