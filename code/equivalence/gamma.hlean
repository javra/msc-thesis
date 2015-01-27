import ..dbl_gpd.basic ..xmod.decl

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod

set_option pp.beta true
namespace gamma
  context
  universe variable l
  parameters {D₀ : Type.{l}}
    [D₀set : is_hset D₀]
    [C : groupoid.{l l} D₀]
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
      Type.{l})
    [G : dbl_gpd C D₂]
  include D₀set C G

  structure M_morphism (a b : D₀) : Type :=
    (discon : a = b)
    (lid : hom a b)
    (filler : D₂ lid (transport (λ x, hom a x) discon (ID a)) id id)

  definition M_morphism.sigma_char (a b : D₀) :
    ( Σ (discon : a = b) (lid : hom a b), D₂ lid (discon ▹ id) id id) ≃ (M_morphism a b) :=
  begin
    fapply equiv.mk,
      intro P, apply (sigma.rec_on P), intros (p, S),
      apply (sigma.rec_on S), intros (lid, filler),
      exact (M_morphism.mk p lid filler),
    fapply is_equiv.adjointify,
        intro P, apply (M_morphism.rec_on P), intros (p, lid, filler),
        exact ((⟨p, lid, filler⟩)),
      intro P, apply (M_morphism.rec_on P), intros (p, lid, filler),
      apply idp,
    intro P, apply (sigma.rec_on P), intros (p, S),
    apply (sigma.rec_on S), intros (lid, filler),
    apply idp,
  end

  protected definition M_morphism.is_hset (a b : D₀) :
    is_hset (M_morphism a b) :=
  begin
    apply trunc_equiv, apply equiv.to_is_equiv, apply M_morphism.sigma_char,
    apply trunc_sigma, apply succ_is_trunc, apply trunc_succ, exact D₀set,
    intro p, apply trunc_sigma, apply !homH,
    intro f, apply (homH' D₂),
  end

  protected definition M_morphism.comp_transport (a b c : D₀) (M : M_morphism b c)
    (N : M_morphism a b) :
    (transport (λ x, hom b x) (M_morphism.discon M) (ID b))
      ∘ (transport (λ x, hom a x) (M_morphism.discon N) (ID a))
          = (transport (λ x, hom a x) ((M_morphism.discon N) ⬝ (M_morphism.discon M)) (ID a)) :=
  begin
    apply inverse, revert M,
    apply (M_morphism.rec_on N), intro discon,
    apply (eq.rec_on discon), intros,
    apply (M_morphism.rec_on M), intro discon',
    apply (eq.rec_on discon'), intros,
    apply (!id_left⁻¹),
  end

  protected definition M : groupoid.{l l} D₀ :=
  begin
    fapply groupoid.mk,
      intros (a, b), exact (M_morphism a b),
      intros (a, b), exact (M_morphism.is_hset a b),
      intros (a, b, c, M, N), fapply M_morphism.mk,
        apply ((M_morphism.discon N) ⬝ (M_morphism.discon M)),
        apply ((M_morphism.lid M) ∘ (M_morphism.lid N)),
        apply ((M_morphism.comp_transport a b c M N) ▹ comp₂ D₂ (M_morphism.filler M) (M_morphism.filler N)),
      intros,  fapply M_morphism.mk,
        apply idp, apply id, apply (ID₂ D₂ id),
      intros,
  end


  end
end gamma
