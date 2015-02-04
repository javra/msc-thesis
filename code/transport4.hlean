open eq

context
  parameters {A B C D : Type} (P : A → B → C → D → Type)

  definition transport4 {a0 a1 : A} {b0 b1 : B} {c0 c1 : C} {d0 d1 : D}
    (pa : a0 = a1) (pb : b0 = b1) (pc : c0 = c1) (pd : d0 = d1)
    (u : P a0 b0 c0 d0) : P a1 b1 c1 d1 :=
  pd ▹ pc ▹ pb ▹ pa ▹ u

  definition transport4_eq_transport {E : Type}
    {f : E → A} {g : E → B} {h : E → C} {i : E → D}
    {e0 e1 : E} (p : e0 = e1)
    (u : P (f e0) (g e0) (h e0) (i e0)) :
    transport (λ (x : E), P (f x) (g x) (h x) (i x)) p u
    = transport4 (ap f p) (ap g p) (ap h p) (ap i p) u :=
  begin
    apply (eq.rec_on p), apply idp,
  end

  definition transport4_acc {a0 a1 a2 : A} {b0 b1 b2 : B} {c0 c1 c2 : C} {d0 d1 d2 : D}
    (pa1 : a0 = a1) (pb1 : b0 = b1) (pc1 : c0 = c1) (pd1 : d0 = d1)
    (pa2 : a1 = a2) (pb2 : b1 = b2) (pc2 : c1 = c2) (pd2 : d1 = d2)
    (u : P a0 b0 c0 d0) :
    transport4 pa2 pb2 pc2 pd2 (transport4 pa1 pb1 pc1 pd1 u)
    = transport4 (pa1 ⬝ pa2) (pb1 ⬝ pb2) (pc1 ⬝ pc2) (pd1 ⬝ pd2) u :=
  begin
    apply (eq.rec_on pa2),
    apply (eq.rec_on pb2),
    apply (eq.rec_on pc2),
    apply (eq.rec_on pd2),
    apply idp,
  end

  definition transport4_transport_acc {E : Type} {a0 : A} {b0 : B} {c0 : C} {d0 : D}
    {e0 e1 : E} {f : E → A} {g : E → B} {h : E → C} {i : E → D}
    (pa : f e1 = a0) (pb : g e1 = b0) (pc : h e1 = c0) (pd : i e1 = d0)
    (p : e0 = e1) (u : P (f e0) (g e0) (h e0) (i e0)) :
  transport4 pa pb pc pd (transport (λ (x : E), P (f x) (g x) (h x) (i x)) p u)
  = transport4 (ap f p ⬝ pa) (ap g p ⬝ pb) (ap h p ⬝ pc) (ap i p ⬝ pd) u :=
  begin
    apply (eq.rec_on pa),
    apply (eq.rec_on pb),
    apply (eq.rec_on pc),
    apply (eq.rec_on pd),
    apply (eq.rec_on p),
    apply idp,
  end

end

exit
                      (transport
                         (λ (a_6 : hom z x),
                            D₂ (compose (compose b a) (compose lid a_6))
                              (compose (compose b a) (compose id a_6))
                              (ID z)
                              (ID z))
                         (inverse (Pbainv D₂ a b))
