import types.pi types.sigma
import .decl

open eq dbl_precat precategory truncation morphism
reducible compose

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

  end
end thin_structure
