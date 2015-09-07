import types.pi types.sigma
import .decl

open eq dbl_precat category is_trunc thin_structure

namespace dbl_gpd
  section
  parameters {D₀ : Type} [C : precategory D₀]
    {D₂ : Π ⦃a b c d : D₀⦄, hom a b → hom c d → hom a c → hom b d → Type}
    (D : dbl_precat C D₂)
    [T : thin_structure D]
  include T

  definition br_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ f (ID b) f (ID b) :=
  thin D f (ID b) f (ID b) idp

  definition ul_connect ⦃a b : D₀⦄ (f : hom a b) : D₂ (ID a) f (ID a) f :=
  thin D (ID a) f (ID a) f idp

  definition br_connect_id_eq_ID₁ (a : D₀) : br_connect (ID a) = ID₁ D (ID a) :=
  begin
    apply inverse, apply concat, apply inverse, apply (thin_id₁ D),
    apply (ap (λ x, thin D _ _ _ _ x)), apply is_hset.elim,
  end

  definition ID₁_of_ul_br_aux {a b : D₀} (f g h : hom a b)
    (p : g = f) (q : h = f)
    (r1 : h ∘ id = id ∘ g) (r2 : f ∘ id = id ∘ f)
    (rr : q ▸ (p ▸ r1) = r2) :
    q ▸ (p ▸ thin D g h id id r1) = thin D f f id id r2 :=
  by cases rr; cases p; cases q; apply idp

  definition ID₁_of_ul_br ⦃a b : D₀⦄ (f : hom a b) :
    (id_left f) ▸ ((id_right f) ▸
    (comp₂ D (br_connect f) (ul_connect f))) = ID₁ D f :=
  begin
    -- Bring transports to right hand side
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    -- Work on left hand side
    apply concat,
      -- Composites of thin squares are thin
      apply (thin_comp₂ D),
      -- Commutativity of composite square
      apply inverse, apply assoc,
    -- Bring transports to left hand side
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply concat,
      -- Apply helper lemma eliminating transports
      apply ID₁_of_ul_br_aux, apply is_hset.elim,
      exact ((id_right f) ⬝ (id_left f)⁻¹),
    -- Identity squares are thin
    apply (thin_id₁ D),
  end

  definition ID₂_of_br_ul_aux {a b : D₀} (f g h : hom a b)
    (p : g = f) (q : h = f)
    (r1 : id ∘ g = h ∘ id) (r2 : id ∘ f = f ∘ id)
    (rr : q ▸ (p ▸ r1) = r2) :
    q ▸ (p ▸ thin D id id g h r1) = thin D id id f f r2 :=
  by cases rr; cases p; cases q; apply idp

  definition ID₂_of_br_ul ⦃a b : D₀⦄ (f : hom a b) :
    (id_left f) ▸ ((id_right f) ▸
    (comp₁ D (br_connect f) (ul_connect f))) = ID₂ D f :=
  begin
    apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
    fapply concat,
      apply (thin_comp₁ D), apply !assoc,
    apply eq_inv_tr_of_tr_eq, apply eq_inv_tr_of_tr_eq,
    apply concat,
      apply !ID₂_of_br_ul_aux, apply is_hset.elim,
      exact ((id_left f) ⬝ (id_right f)⁻¹),
    apply (thin_id₂ D),
  end

  definition br_of_br_square_aux {a c : D₀} (gf : hom a c)
    (h₁ h₁' : hom c c) (p : h₁ = ID c) (p' : h₁' = ID c)
    (r1 : h₁ ∘ gf = h₁' ∘ gf) (r2 : (ID c) ∘ gf = (ID c) ∘ gf) :
    (p' ▸ p ▸ thin D gf h₁ gf h₁' r1) = thin D gf (ID c) gf (ID c) r2 :=
  by cases p'; cases p; apply (ap (λ x, thin D _ _ _ _ x) !is_hset.elim)

  definition br_of_br_square ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c) :
    (transport (λ x, D₂ _ _ _ x) (id_left id)
     (transport (λ x, D₂ _ x _ _) (id_left id)
      (comp₁ D (comp₂ D (br_connect g) (ID₂ D g))
       (comp₂ D (ID₁ D g) (br_connect f)))))
    = br_connect (g ∘ f) :=
  begin
    do 2 (apply tr_eq_of_eq_inv_tr),
    -- Prove commutativity of second row
    assert line2_commute : (id ∘ id) ∘ g = id ∘ g ∘ id,
      exact (calc (id ∘ id) ∘ g = id ∘ g : by rewrite id_left
                           ... = (id ∘ g) ∘ id : by rewrite id_right
                           ... = id ∘ (g ∘ id) : assoc),
    -- Prove thinness of second row
    assert line2_thin : comp₂ D (br_connect g) (ID₂ D g)
      = thin D (g ∘ id) (id ∘ id) g id line2_commute,
      apply concat, apply (ap (λx, comp₂ D _ x)), apply inverse, apply thin_id₂,
      apply thin_comp₂,
    -- Prove commutativity of first row
    assert line1_commute : (g ∘ id) ∘ f = id ∘ g ∘ f,
      exact (calc (g ∘ ID b) ∘ f = g ∘ f : by rewrite id_right
                            ... = ID c ∘ g ∘ f : id_left),
    -- Prove thinness of first row
    assert line1_thin : comp₂ D (ID₁ D g) (br_connect f)
      = thin D (g ∘ f) (g ∘ id) f id line1_commute,
      apply concat, apply (ap (λx, comp₂ D x _)), apply inverse, apply thin_id₁,
      apply thin_comp₂,
    -- Replace composite squares by thin squares
    apply concat, exact (ap (λx, comp₁ D x _) line2_thin),
    apply concat, exact (ap (λx, comp₁ D _ x) line1_thin),
    -- Thinness of the entire 2x2 grid
    apply concat, apply (thin_comp₁ D), apply idp,
    do 2 (apply eq_inv_tr_of_tr_eq),
    apply br_of_br_square_aux,
  end

  definition ul_of_ul_square_aux {b d : D₀} (ih : hom b d)
    (f₁ : hom b b) (p : f₁ = ID b)
    (r1 : ih ∘ f₁ = ih ∘ f₁) (r2 : ih ∘ (ID b) = ih ∘ (ID b)) :
    (p ▸ thin D f₁ ih f₁ ih r1) = thin D (ID b) ih (ID b) ih r2 :=
  by cases p; apply (ap (λ x, thin D _ _ _ _ x) !is_hset.elim)

  definition ul_of_ul_square ⦃a b c : D₀⦄ (f : hom a b) (g : hom b c) :
    (id_left (ID a)) ▸
    (comp₂ D (comp₁ D (ul_connect g) (ID₂ D f)) (comp₁ D (ID₁ D f) (ul_connect f)))
    = ul_connect (g ∘ f) :=
  begin
    apply tr_eq_of_eq_inv_tr,
    assert col1_commute : f ∘ id ∘ id = (id ∘ f) ∘ id,
      exact (calc f ∘ id ∘ id = f ∘ id : by rewrite id_left
                         ... = id ∘ (f ∘ id) : id_left
                         ... = (id ∘ f) ∘ id : assoc),
    assert col1_thin : comp₁ D (ID₁ D f) (ul_connect f)
      = thin D id f (id ∘ id) (id ∘ f) col1_commute,
      apply concat, apply (ap (λx, comp₁ D x _)), apply inverse, apply thin_id₁,
      apply (thin_comp₁ D),
    assert col2_commute : g ∘ id ∘ f = (g ∘ f) ∘ id,
      exact (calc g ∘ id ∘ f = g ∘ f : by rewrite id_left
                        ... = (g ∘ f) ∘ id : id_right),
    assert col2_thin : comp₁ D (ul_connect g) (ID₂ D f)
      = thin D id g (id ∘ f) (g ∘ f) col2_commute,
      apply concat, apply (ap (λx, comp₁ D _ x)), apply inverse, apply thin_id₂,
      apply thin_comp₁,
    apply concat, exact (ap (λx, comp₂ D _ x) col1_thin),
    apply concat, exact (ap (λx, comp₂ D x _) col2_thin),
    apply concat, apply (thin_comp₂ D), apply idp,
    apply eq_inv_tr_of_tr_eq,
    apply ul_of_ul_square_aux,
  end

  end
end dbl_gpd
