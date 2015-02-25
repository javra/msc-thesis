import .decl
import algebra.precategory.functor

open eq functor precategory morphism dbl_precat functor Dbl_precat
set_option pp.beta true

namespace dbl_precat

  check ID₁
  variables (D E : Dbl_precat)
  include D E
  variables (a b : cat D) (f : hom a b) (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))
  check (twoF (ID₁ (two_cell D) f))
  check transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
    (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
    (twoF (ID₁ (two_cell D) f)))
   = (ID₁ (two_cell E) (catF f))
  check (respect_id catF a)

  definition respect_id₁_type : Type := Π ⦃a b : cat D⦄ ⦃f : hom a b⦄,
      transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
        (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
          (twoF (ID₁ (two_cell D) f)))
      = (ID₁ (two_cell E) (catF f))


exit
  structure dbl_functor (D E : Dbl_precat) :=
    (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))
    (respect_id₁ : Π ⦃a b : cat D⦄ ⦃f : hom a b⦄,
      transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
        (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
          (twoF (ID₁ (two_cell D) f)))
      = (ID₁ (two_cell E) (catF f)))

end dbl_precat




exit
  (obF : C → D)
  (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b))
  (respect_id : Π (a : C), homF (ID a) = ID (obF a))
  (respect_comp : Π {a b c : C} (g : hom b c) (f : hom a b),
    homF (g ∘ f) = homF g ∘ homF f)
