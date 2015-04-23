import .decl ..transport4
import algebra.precategory.functor

open eq functor category dbl_precat functor
open Dbl_precat prod equiv sigma.ops is_trunc

set_option pp.beta true

namespace dbl_precat

  section
  variables (D E : Dbl_precat)
  include D E
  variables (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))

  definition respect_id₁_type [reducible] : Type := Π ⦃a b : cat D⦄ (f : hom a b),
    transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
      (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
        (twoF (ID₁ (two_cell D) f)))
    = ID₁ (two_cell E) (catF f)

  definition respect_id₂_type [reducible] : Type := Π ⦃a b : cat D⦄ (f : hom a b),
    transport (λ x, two_cell E _ x _ _) (respect_id catF b)
      (transport (λ x, two_cell E x _ _ _) (respect_id catF a)
        (twoF (ID₂ (two_cell D) f)))
    = ID₂ (two_cell E) (catF f)

  set_option unifier.max_steps 80000 --TODO make this go away
  definition respect_comp₁_type [reducible] : Type := Π ⦃a b c₁ d₁ c₂ d₂ : cat D⦄
    ⦃f : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : two_cell D g₁ g₂ h₂ i₂)
    (u : two_cell D f g₁ h₁ i₁),
      transport
        (λ x, two_cell E (to_fun_hom catF f) (to_fun_hom catF g₂) (to_fun_hom catF h₂ ∘ to_fun_hom catF h₁) x)
        (respect_comp catF i₂ i₁)
        (transport
          (λ x, two_cell E (to_fun_hom catF f) (to_fun_hom catF g₂) x (to_fun_hom catF (i₂ ∘ i₁)))
          (respect_comp catF h₂ h₁)
          (twoF (comp₁ (two_cell D) v u)))
      = comp₁ (two_cell E) (@twoF c₁ d₁ c₂ d₂ g₁ g₂ h₂ i₂ v) (twoF u)

  definition respect_comp₂_type [reducible] : Type := Π ⦃a b₁ c d₁ b₂ d₂ : cat D⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : two_cell D f₂ g₂ i₁ i₂)
    (u : two_cell D f₁ g₁ h i₁),
      transport
        (λ x, two_cell E (to_fun_hom catF f₂ ∘ to_fun_hom catF f₁) x (to_fun_hom catF h) (to_fun_hom catF i₂))
        (respect_comp catF g₂ g₁)
        (transport
          (λ x, two_cell E x (to_fun_hom catF (g₂ ∘ g₁)) (to_fun_hom catF h) (to_fun_hom catF i₂))
          (respect_comp catF f₂ f₁)
          (twoF (comp₂ (two_cell D) v u)))
      = comp₂ (two_cell E) (twoF v) (twoF u)
  set_option unifier.max_steps 20000
  end

  structure dbl_functor (D E : Dbl_precat) :=
    (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))
    (respect_id₁ : respect_id₁_type D E catF twoF)
    (respect_comp₁ : respect_comp₁_type D E catF twoF)
    (respect_id₂ : respect_id₂_type D E catF twoF)
    (respect_comp₂ : respect_comp₂_type D E catF twoF)

  definition dbl_functor_sigma_char (D E : Dbl_precat) :
    (Σ (catF : functor (cat D) (cat E))
       (twoF : Π ⦃a b c d : cat D⦄
         ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
         two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i)),
       (respect_id₁_type D E catF twoF) ×
       (respect_comp₁_type D E catF twoF) ×
       (respect_id₂_type D E catF twoF) ×
       (respect_comp₂_type D E catF twoF)) ≃ (dbl_functor D E) :=
  begin
    fapply equiv.mk,
      begin
        intro S, fapply dbl_functor.mk,
        apply (S.1), exact (@S.2.1), exact (pr1 @S.2.2),
        exact (pr1 (pr2 @S.2.2)), exact (pr1 (pr2 (pr2 @S.2.2))),
        exact (pr2 (pr2 (pr2 @S.2.2)))
      end,
      begin
        fapply is_equiv.adjointify,
          {intro F, cases F,
           apply (sigma.mk catF (sigma.mk twoF
                   (respect_id₁ , (respect_comp₁, (respect_id₂, respect_comp₂)))))},
          {intro F, cases F, apply idp},
          {intro S,
           cases S    with [catF, S'],
           cases S'   with [twoF, S''],
           cases S''  with [respect_id₁, S'''],
           cases S''' with [respect_comp₁, S''''],
           cases S'''',
           apply idp}
      end
  end

  section
  parameters (D E : Dbl_precat)
    (catF1 catF2 : functor (cat D) (cat E))
    (twoF1 : Π ⦃a b c d : cat D⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF1 f) (catF1 g) (catF1 h) (catF1 i))
    (twoF2 : Π ⦃a b c d : cat D⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF2 f) (catF2 g) (catF2 h) (catF2 i))

  definition respect_id₁1_type [reducible] := respect_id₁_type D E catF1
  definition respect_id₁2_type [reducible] := respect_id₁_type D E catF2
  definition respect_comp₁1_type [reducible] := respect_comp₁_type D E catF1
  definition respect_comp₁2_type [reducible] := respect_comp₁_type D E catF2
  definition respect_id₂1_type [reducible] := respect_id₂_type D E catF1
  definition respect_id₂2_type [reducible] := respect_id₂_type D E catF2
  definition respect_comp₂1_type [reducible] := respect_comp₂_type D E catF1
  definition respect_comp₂2_type [reducible] := respect_comp₂_type D E catF2

  definition dbl_functor.congr (p1 : catF1 = catF2) (p2 : p1 ▹ twoF1 = twoF2) :
    Π (respect_id₁1 : respect_id₁1_type twoF1)
    (respect_id₁2 : respect_id₁2_type twoF2)
    (respect_comp₁1 : respect_comp₁1_type twoF1)
    (respect_comp₁2 : respect_comp₁2_type twoF2)
    (respect_id₂1 : respect_id₂1_type twoF1)
    (respect_id₂2 : respect_id₂2_type twoF2)
    (respect_comp₂1 : respect_comp₂1_type twoF1)
    (respect_comp₂2 : respect_comp₂2_type twoF2),
    dbl_functor.mk catF1 twoF1 respect_id₁1 respect_comp₁1 respect_id₂1 respect_comp₂1
    = dbl_functor.mk catF2 twoF2 respect_id₁2 respect_comp₁2 respect_id₂2 respect_comp₂2 :=
  begin
    apply (eq.rec_on p2), apply (eq.rec_on p1),
    intros, apply (ap01111 (λ f g h i, dbl_functor.mk catF1 twoF1 f g h i)),
      repeat (
        repeat ( apply eq_of_homotopy ; intros ) ;
        apply (@is_hset.elim _ (!(homH' (two_cell E)))) ),
  end

  end

  open dbl_functor

  definition respect_id₁' {D E : Dbl_precat} (F : dbl_functor D E)
    {a b : cat D} (f : hom a b) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (respect_id₁ F f))

  definition respect_id₂' {D E : Dbl_precat} (F : dbl_functor D E)
    {a b : cat D} (f : hom a b) :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (respect_id₂ F f))

  section
  parameters {D E : Dbl_precat} (F : dbl_functor D E)
    ⦃a b c₁ d₁ c₂ d₂ : cat D⦄
    ⦃f : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : two_cell D g₁ g₂ h₂ i₂)
    (u : two_cell D f g₁ h₁ i₁)

  definition respect_comp₁' :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (respect_comp₁ F v u))

  end

  section
  parameters {D E : Dbl_precat} (F : dbl_functor D E)
    ⦃a b₁ c d₁ b₂ d₂ : cat D⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : two_cell D f₂ g₂ i₁ i₂)
    (u : two_cell D f₁ g₁ h i₁)

  definition respect_comp₂' :=
  eq_inv_tr_of_tr_eq _ _ _ _
    (eq_inv_tr_of_tr_eq _ _ _ _ (respect_comp₂ F v u))

  end

  section
  parameters
    {D E : Dbl_precat} (F : dbl_functor D E)
    {a b c d : cat D}
    {f f': hom a b} {g g': hom c d} {h h': hom a c} {i i': hom b d}
    (pf : f = f') (pg : g = g') (ph : h = h') (pi : i = i')
    (u : two_cell D f g h i)

  definition twoF_transport_u : twoF F (pf ▹ u) = pf ▹ (twoF F u) :=
  begin
    apply (eq.rec_on pf), apply idp,
  end

  definition twoF_transport_b : twoF F (pg ▹ u) = pg ▹ (twoF F u) :=
  begin
    apply (eq.rec_on pg), apply idp,
  end

  definition twoF_transport_l : twoF F (ph ▹ u) = ph ▹ (twoF F u) :=
  begin
    apply (eq.rec_on ph), apply idp,
  end

  definition twoF_transport_r : twoF F (pi ▹ u) = pi ▹ (twoF F u) :=
  begin
    apply (eq.rec_on pi), apply idp,
  end

  end

  definition dbl_functor_compose [reducible] {C D E : Dbl_precat}
    (G : dbl_functor D E) (F : dbl_functor C D) : dbl_functor C E :=
  begin
    fapply dbl_functor.mk,
      apply (functor.compose (catF G) (catF F)),
      intros, apply (twoF G (twoF F a_1)),
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_id₁',
        apply concat, apply twoF_transport_l, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_r, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_id₁',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        apply inverse,
        apply concat, apply (transport_eq_transport4 _
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) f))
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) f))
          (λ x, ID (to_fun_ob (catF G) (to_fun_ob (catF F) a))) (λ x, x)),
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_comp₁',
        apply concat, apply twoF_transport_l, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_r, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_comp₁',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        unfold functor.compose, esimp,
        apply inverse,
        apply concat, apply (transport_eq_transport4 _
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) f))
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) g₂))
          (λ x, comp (to_fun_hom (catF G) (to_fun_hom (catF F) h₂))
            (to_fun_hom (catF G) (to_fun_hom (catF F) h₁)))
          (λ x, x)),
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_id₂',
        apply concat, apply twoF_transport_u, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_b, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_id₂',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        apply inverse,
        apply concat, apply (transport_eq_transport4 _
          (λ x, ID (to_fun_ob (catF G) (to_fun_ob (catF F) a))) (λ x, x)
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) f))
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) f))),
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply transport4_set_reduce,
      intros, apply tr_eq_of_eq_inv_tr, apply tr_eq_of_eq_inv_tr,
        apply concat, apply (ap (λ x, twoF G x)), apply respect_comp₂',
        apply concat, apply twoF_transport_u, apply tr_eq_of_eq_inv_tr,
        apply concat, apply twoF_transport_b, apply tr_eq_of_eq_inv_tr,
        apply concat, apply respect_comp₂',
        apply inv_tr_eq_of_eq_tr, apply inv_tr_eq_of_eq_tr,
        unfold functor.compose, esimp,
        apply inverse,
        apply concat, apply (transport_eq_transport4 _
          (λ x, comp (to_fun_hom (catF G) (to_fun_hom (catF F) _))
            (to_fun_hom (catF G) (to_fun_hom (catF F) _)))
          (λ x, x)
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) _))
          (λ x, to_fun_hom (catF G) (to_fun_hom (catF F) _))),
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply concat, apply transport4_transport_acc,
        apply transport4_set_reduce,
  end

  definition dbl_functor_id (C : Dbl_precat) : dbl_functor C C :=
  begin
    fapply dbl_functor.mk,
      apply functor.id,
      intros, apply a_1,
      intros, apply idp,
      intros, apply idp,
      intros, apply idp,
      intros, apply idp,
  end

  section
  parameters
    {B E : Dbl_precat}
    (F1 G1 : functor (cat B) (cat E))
    (p : F1 = G1)
    (F2 : Π ⦃a b c d : carrier (cat B)⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell B f g h i →
      two_cell E (to_fun_hom F1 f) (to_fun_hom F1 g) (to_fun_hom F1 h) (to_fun_hom F1 i))

  abbreviation G2 [reducible] := transport
    (λ H, Π ⦃a b c d : carrier (cat B)⦄
      ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell B f g h i →
      two_cell E (to_fun_hom H f) (to_fun_hom H g) (to_fun_hom H h) (to_fun_hom H i))
    p F2

  abbreviation dbl_functor_assoc_aux_lhs :=
  (transport
    (λ (a : functor (cat B) (cat E)),
       Π ⦃a_1 b c d : carrier (cat B)⦄
       ⦃f : hom a_1 b⦄ ⦃g : hom c d⦄ ⦃h : hom a_1 c⦄ ⦃i : hom b d⦄,
       two_cell B f g h i →
       two_cell E (to_fun_hom a f) (to_fun_hom a g) (to_fun_hom a h) (to_fun_hom a i))
       p
       (λ ⦃a b c d : carrier (cat B)⦄
         ⦃f : hom a b⦄ ⦃g : hom  c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
         (a_1 : two_cell B f g h i), F2 a_1))

  abbreviation dbl_functor_assoc_aux_rhs :=
  λ ⦃a b c d : carrier (cat B)⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom  b d⦄
    (a_1 : two_cell B f g h i), G2 a_1

  definition dbl_functor_assoc_aux1 :
    dbl_functor_assoc_aux_lhs = dbl_functor_assoc_aux_rhs :=
  begin
    cases p, apply idp,
  end

  end
exit
  set_option pp.notation false
  --set_option unifier.max_steps 50000
  definition dbl_functor_assoc{B C D E : Dbl_precat}
    (H : dbl_functor D E) (G : dbl_functor C D) (F : dbl_functor B C) :
    dbl_functor_compose H (dbl_functor_compose G F)
    = dbl_functor_compose (dbl_functor_compose H G) F :=
  begin
    fapply (dbl_functor.congr B E),
      apply functor.assoc,
    --unfold dbl_functor_compose, esimp,
    /-cases F with (F1, F2, F3, F4, F5, F6),
    cases G with (G1, G2, G3, G4, G5, G6),
    cases H with (H1, H2, H3, H4, H5, H6),
    cases F1 with (F11, F12, F13, F14),
    cases G1 with (G11, G12, G13, G14),
    cases H1 with (H11, H12, H13, H14),
    unfold catF, unfold to_fun_hom, esimp,-/
    /-apply (dbl_functor_assoc_aux1
      (dbl_functor_compose H (dbl_functor_compose G F))
      (dbl_functor_compose (dbl_functor_compose H G) F)),-/
    unfold catF, unfold dbl_functor_compose, esimp,
    exact sorry,
  end

end dbl_precat

exit
