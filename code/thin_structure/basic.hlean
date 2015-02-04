import types.pi types.sigma
import .decl

open eq dbl_precat precategory truncation morphism
attribute compose [reducible]

namespace thin_structure
  context
  parameters {D₀ : Type} [C : precategory D₀]
  {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type} [D : dbl_precat C D₂]
  {thin : Π ⦃a b c d : D₀⦄
    (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), g ∘ h = i ∘ f → D₂ f g h i}
  [T : thin_structure D₂ thin]

  definition br_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ f (ID b) f (ID b) :=
  thin f (ID b) f (ID b) idp

  definition ul_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID a) f (ID a) f :=
  thin (ID a) f (ID a) f idp

  include D T

  definition ID₁_of_ul_br_aux {a b : D₀} (f g h : hom a b)
    (p : g = f) (q : h = f)
    (r1 : h ∘ id = id ∘ g) (r2 : f ∘ id = id ∘ f)
    (rr : q ▹ (p ▹ r1) = r2) :
    q ▹ (p ▹ thin g h id id r1) = thin f f id id r2 :=
  eq.rec_on rr (eq.rec_on p (eq.rec_on q idp))

  definition ID₁_of_ul_br ⦃a b : D₀⦄ (f : hom a b) :
    (id_left f) ▹ ((id_right f) ▹
    (comp₂ D₂ (br_connect f) (ul_connect f))) = ID₁ D₂ f :=
  begin
    apply moveR_transport_p, apply moveR_transport_p,
    fapply concat,
      apply (thin_structure.thin_comp₂ D thin),
      apply inverse, apply !assoc,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat,
      apply !ID₁_of_ul_br_aux,
      apply is_hset.elim,
      exact ((id_right f) ⬝ (id_left f)⁻¹),
    apply (thin_structure.thin_id₁ D thin),
  end

  definition ID₂_of_br_ul_aux {a b : D₀} (f g h : hom a b)
    (p : g = f) (q : h = f)
    (r1 : id ∘ g = h ∘ id) (r2 : id ∘ f = f ∘ id)
    (rr : q ▹ (p ▹ r1) = r2) :
    q ▹ (p ▹ thin id id g h r1) = thin id id f f r2 :=
  eq.rec_on rr (eq.rec_on p (eq.rec_on q idp))

  definition ID₂_of_br_ul ⦃a b : D₀⦄ (f : hom a b) :
    (id_left f) ▹ ((id_right f) ▹
    (comp₁ D₂ (br_connect f) (ul_connect f))) = ID₂ D₂ f :=
  begin
    apply moveR_transport_p, apply moveR_transport_p,
    fapply concat,
      apply (thin_structure.thin_comp₁ D thin),
      apply !assoc,
    apply moveL_transport_V, apply moveL_transport_V,
    apply concat,
      apply !ID₂_of_br_ul_aux,
      apply is_hset.elim,
      exact ((id_left f) ⬝ (id_right f)⁻¹),
    apply (thin_structure.thin_id₂ D thin),
  end

  --TODO: make this waay shorter!
  definition br_of_br_square_aux_aux {a c : D₀} (gf : hom a c)
    (h₁ : hom c c) (p : h₁ = ID c)
    (r1 : h₁ ∘ gf = h₁ ∘ gf) (r2 : (ID c) ∘ gf = (ID c) ∘ gf)
    (rr : (p ▹ r1) = r2) :
    (p ▹ thin gf h₁ gf h₁ r1) = thin gf (ID c) gf (ID c) r2 :=
  eq.rec_on rr (eq.rec_on p idp)

  definition br_of_br_square_aux ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c)
    (p : ID c ∘ ID c = ID c) :
    transport (λ x, D₂ (g ∘ f) x (g ∘ f) x)
      p (thin (g ∘ f) (ID c ∘ ID c) (g ∘ f) (ID c ∘ ID c)
    (refl ((ID c ∘ ID c) ∘ g ∘ f))) = br_connect (g ∘ f) :=
  begin
    apply br_of_br_square_aux_aux,
    apply @is_hset.elim, apply !homH,
  end

  definition br_of_br_square ⦃a b c : D₀⦄ (f : @hom D₀ C a b) (g : @hom D₀ C  b c) :
    (@id_left D₀ C c c (ID c)) ▹
    (comp₁ D₂ (comp₂ D₂ (br_connect g) (ID₂ D₂ g)) (comp₂ D₂ (ID₁ D₂ g) (br_connect f)))
      = br_connect (g ∘ f) :=
  begin
    apply moveR_transport_p,
    assert (line2_commute : (id ∘ id) ∘ g = id ∘ g ∘ id),
      exact (calc (id ∘ id) ∘ g = id ∘ g : @id_left D₀ C
                           ... = (id ∘ g) ∘ id : id_right
                           ... = id ∘ (g ∘ id) : assoc),
    assert (line2_thin : thin (g ∘ id) (id ∘ id) g id line2_commute = comp₂ D₂ (br_connect g) (ID₂ D₂ g)),
      assert (line2_aux : ID₂ D₂ g = thin id id g g (!id_left ⬝ !id_right⁻¹)),
        apply inverse, apply (thin_structure.thin_id₂ D thin),
      apply inverse, apply concat, exact (ap (λx, comp₂ D₂ (br_connect g) x) line2_aux),
      apply (thin_structure.thin_comp₂ D thin),
    assert (line1_commute : (g ∘ id) ∘ f = id ∘ g ∘ f),
      exact (calc (g ∘ ID b) ∘ f = g ∘ f : @id_right D₀ C
                            ... = ID c ∘ g ∘ f : id_left),
    assert (line1_thin : thin (g ∘ f) (g ∘ id) f id line1_commute = comp₂ D₂ (ID₁ D₂ g) (br_connect f)),
      assert (line1_aux : ID₁ D₂ g = thin g g id id (!id_right ⬝ !id_left⁻¹)),
        apply inverse, apply (thin_structure.thin_id₁ D thin),
      apply inverse, apply concat, exact (ap (λx, comp₂ D₂ x (br_connect f)) line1_aux),
      apply (thin_structure.thin_comp₂ D thin),
    apply concat, exact (ap (λx, comp₁ D₂ x (comp₂ D₂ (ID₁ D₂ g) (br_connect f))) (line2_thin⁻¹)),
    apply concat, exact (ap (λx, comp₁ D₂ (thin (g ∘ id) (id ∘ id) g id line2_commute) x) (line1_thin⁻¹)),
    apply concat, apply (thin_structure.thin_comp₁ D thin),
      apply idp,
    apply moveL_transport_V,
    apply br_of_br_square_aux,
  end

  definition ul_of_ul_square_aux_aux {b d : D₀} (ih : hom b d)
    (f₁ : hom b b) (p : f₁ = ID b)
    (r1 : ih ∘ f₁ = ih ∘ f₁) (r2 : ih ∘ (ID b) = ih ∘ (ID b))
    (rr : (p ▹ r1) = r2) :
    (p ▹ thin f₁ ih f₁ ih r1) = thin (ID b) ih (ID b) ih r2 :=
  eq.rec_on rr (eq.rec_on p idp)

  definition ul_of_ul_square_aux ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c)
    (p : ID a ∘ ID a = ID a) :
    transport (λ x, D₂ x (g ∘ f) x (g ∘ f))
      p (thin (ID a ∘ ID a) (g ∘ f) (ID a ∘ ID a) (g ∘ f)
    (refl ((g ∘ f) ∘ (ID a ∘ ID a)))) = ul_connect (g ∘ f) :=
  begin
    apply ul_of_ul_square_aux_aux,
    apply @is_hset.elim, apply !homH,
  end

  definition ul_of_ul_square ⦃a b c : D₀⦄ (f : @hom D₀ C a b) (g : @hom D₀ C  b c) :
    (@id_left D₀ C a a (ID a)) ▹
    (comp₂ D₂ (comp₁ D₂ (ul_connect g) (ID₂ D₂ f)) (comp₁ D₂ (ID₁ D₂ f) (ul_connect f)))
      = ul_connect (g ∘ f) :=
  begin
    apply moveR_transport_p,
    assert (col1_commute : f ∘ id ∘ id = (id ∘ f) ∘ id),
      exact (calc f ∘ id ∘ id = f ∘ id : @id_left D₀ C
                         ... = id ∘ (f ∘ id) : id_left
                         ... = (id ∘ f) ∘ id : assoc),
    assert (col1_thin : thin id f (id ∘ id) (id ∘ f) col1_commute = comp₁ D₂ (ID₁ D₂ f) (ul_connect f)),
      assert (col1_aux : ID₁ D₂ f = thin f f id id (!id_right ⬝ !id_left⁻¹)),
        apply inverse, apply (thin_structure.thin_id₁ D thin),
      apply inverse, apply concat, exact (ap (λx, comp₁ D₂ x (ul_connect f)) col1_aux),
      apply (thin_structure.thin_comp₁ D thin),
    assert (col2_commute : g ∘ id ∘ f = (g ∘ f) ∘ id),
      exact (calc g ∘ id ∘ f = g ∘ f : @id_left D₀ C
                        ... = (g ∘ f) ∘ id : id_right),
    assert (col2_thin : thin id g (id ∘ f) (g ∘ f) col2_commute = comp₁ D₂ (ul_connect g) (ID₂ D₂ f)),
      assert (col2_aux : ID₂ D₂ f = thin id id f f (!id_left ⬝ !id_right⁻¹)),
        apply inverse, apply (thin_structure.thin_id₂ D thin),
      apply inverse, apply concat, exact (ap (λx, comp₁ D₂ (ul_connect g) x) col2_aux),
      apply (thin_structure.thin_comp₁ D thin),
    apply concat, exact (ap (λx, comp₂ D₂ (comp₁ D₂ (ul_connect g) (ID₂ D₂ f)) x) (col1_thin⁻¹)),
    apply concat, exact (ap (λx, comp₂ D₂ x (thin id f (id ∘ id) (id ∘ f) col1_commute)) (col2_thin⁻¹)),
    apply concat, apply (thin_structure.thin_comp₂ D thin),
      apply idp,
    apply moveL_transport_V,
    apply ul_of_ul_square_aux,
  end

  end
end thin_structure
