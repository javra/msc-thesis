import ..dbl_gpd.basic ..xmod.decl

open dbl_precat precategory truncation eq nat
open equiv groupoid morphism sigma sigma.ops prod
open path_algebra

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

  structure M_morphism (a : D₀) : Type :=
    (lid : hom a a)
    (filler : D₂ lid id id id)

  definition M_morphism.sigma_char (a : D₀) :
    (Σ (lid : hom a a), D₂ lid id id id) ≃ (M_morphism a) :=
  begin
    fapply equiv.mk,
      intro P, apply (sigma.rec_on P), intros (lid, filler),
      exact (M_morphism.mk lid filler),
    fapply is_equiv.adjointify,
        intro P, apply (M_morphism.rec_on P), intros (lid, filler),
        exact ((⟨lid, filler⟩)),
      intro P, apply (M_morphism.rec_on P), intros (lid, filler),
      apply idp,
    intro P, apply (sigma.rec_on P), intros (lid, filler),
    apply idp,
  end

  protected definition M_morphism.is_hset (a : D₀) :
    is_hset (M_morphism a) :=
  begin
    apply trunc_equiv, apply equiv.to_is_equiv, apply M_morphism.sigma_char,
    apply trunc_sigma, apply !homH,
    intro f, apply (homH' D₂),
  end

  protected definition M_morphism.comp [reducible] {a: D₀} (M N : M_morphism a) : M_morphism a :=
  M_morphism.mk ((M_morphism.lid M) ∘ (M_morphism.lid N))
    (transport (λ x, D₂ ((M_morphism.lid M) ∘ (M_morphism.lid N)) x id id)
    (id_left (ID a)) (comp₂ D₂ (M_morphism.filler M) (M_morphism.filler N)))

  protected definition M_morphism.congr ⦃a : D₀⦄
    (f1 g1 : hom a a) (f2 : D₂ f1 id id id) (g2 : D₂ g1 id id id)
    (p1 : f1 = g1) (p2 :  p1 ▹ f2 = g2) :
      M_morphism.mk f1 f2 = M_morphism.mk g1 g2 :=
  begin
    apply (eq.rec_on p2),
    apply (eq.rec_on p1),
    apply idp,
  end

  protected definition M_morphism.assoc ⦃a b c d : D₀⦄ (M N O : M_morphism a) :
    M_morphism.comp M (M_morphism.comp N O) = M_morphism.comp (M_morphism.comp M N) O :=
  begin
    revert O, revert N, apply (M_morphism.rec_on M), intros (M1, M2),
    intro N, apply (M_morphism.rec_on N), intros (N1, N2),
    intro O, apply (M_morphism.rec_on O), intros (M1, M2),
    fapply M_morphism.congr,
      apply !assoc,
      exact sorry,
  end

  protected definition M_morphism.one [reducible] (a : D₀) : M_morphism a :=
  begin
    fapply M_morphism.mk, apply (ID a), apply (ID₂ D₂ (ID a)),
  end

  definition transport_commute {A B : Type} {P : A → B → Type}
    {a a' : A} (p : a = a') {b b' : B} (q : b = b') :
    p ▹ q ▹ P a b = q ▹ p ▹ P a b :=
  begin
    apply (eq.rec_on p), apply (eq.rec_on q), apply idp,
  end

  print definition id_left₁_type
  check @id_left₂
  protected definition M_Morphism.id_left ⦃a : D₀⦄ (M : M_morphism a) :
    M_morphism.comp (M_morphism.one a) M = M :=
  begin
    apply (M_morphism.rec_on M), intros (lid, filler),
    fapply (M_morphism.congr),
      apply (id_left lid),
      --assert (foo : id_left lid ▹ id_left (ID a) ▹ comp₂ D₂ (ID₂ D₂ (ID a)) filler = filler),
      apply (@id_left₂ D₀ C D₂ G a a a a (ID a) (ID a) lid (ID a) filler),
  end

  variables (a : D₀) (lid : hom a a) (filler : D₂ lid id id id)  (M : M_morphism a)
  check (@id_left₂ D₀ C D₂ G a a a a (ID a) (ID a) lid (ID a) filler)
exit
  protected definition M (a : D₀) : group (M_morphism a) :=
  begin
    fapply group.mk,
      intros (u, v), apply (M_morphism.comp u v),
      apply (M_morphism.is_hset a),
      intros (u, v, w), apply ((M_morphism.assoc u v w)⁻¹),
      fapply M_morphism.mk, apply (ID a), apply (ID₂ D₂ (ID a)),

  end


  end
end gamma

    /-fapply groupoid.mk,
      intros (a, b), exact (M_morphism a b),
      intros (a, b), exact (M_morphism.is_hset a b),
      intros (a, b, c, M, N), exact (@M_morphism.comp a b c M N),
      intros,  fapply M_morphism.mk,
        apply idp, apply id, apply (ID₂ D₂ id),-/
      --intros (a, b, c, d, M),
