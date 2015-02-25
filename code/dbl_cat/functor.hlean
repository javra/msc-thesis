import .decl
import algebra.precategory.functor

open eq functor precategory morphism dbl_precat functor Dbl_precat
set_option pp.beta true

namespace dbl_precat

  variables (D E : Dbl_precat)
  include D E
  variables (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))

  definition respect_id₁_type : Type := Π ⦃a b : cat D⦄ ⦃f : hom a b⦄,
    transport (λ x, two_cell E _ _ _ x) (respect_id catF b)
      (transport (λ x, two_cell E _ _ x _) (respect_id catF a)
        (twoF (ID₁ (two_cell D) f)))
    = ID₁ (two_cell E) (catF f)

  definition respect_id₂_type : Type := Π ⦃a b : cat D⦄ ⦃f : hom a b⦄,
    transport (λ x, two_cell E _ x _ _) (respect_id catF b)
      (transport (λ x, two_cell E x _ _ _) (respect_id catF a)
        (twoF (ID₂ (two_cell D) f)))
    = ID₂ (two_cell E) (catF f)

  set_option unifier.max_steps 80000 --TODO make this go away
  definition respect_comp₁_type : Type := Π ⦃a b c₁ d₁ c₂ d₂ : cat D⦄
    ⦃f : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    (v : two_cell D g₁ g₂ h₂ i₂)
    (u : two_cell D f g₁ h₁ i₁),
      transport
        (λ x, two_cell E (homF catF f) (homF catF g₂) (homF catF h₂ ∘ homF catF h₁) x)
        (respect_comp catF i₂ i₁)
        (transport
          (λ x, two_cell E (homF catF f) (homF catF g₂) x (homF catF (i₂ ∘ i₁)))
          (respect_comp catF h₂ h₁)
          (twoF (comp₁ (two_cell D) v u)))
      = comp₁ (two_cell E) (@twoF c₁ d₁ c₂ d₂ g₁ g₂ h₂ i₂ v) (twoF u)

  definition respect_comp₂_type : Type := Π ⦃a b₁ c d₁ b₂ d₂ : cat D⦄
    ⦃f₁ : hom a b₁⦄ ⦃g₁ : hom c d₁⦄ ⦃h : hom a c⦄ ⦃i₁ : hom b₁ d₁⦄
    ⦃f₂ : hom b₁ b₂⦄ ⦃g₂ : hom d₁ d₂⦄ ⦃i₂ : hom b₂ d₂⦄
    (v : two_cell D f₂ g₂ i₁ i₂)
    (u : two_cell D f₁ g₁ h i₁),
      transport
        (λ x, two_cell E (homF catF f₂ ∘ homF catF f₁) x (homF catF h) (homF catF i₂))
        (respect_comp catF g₂ g₁)
        (transport
          (λ x, two_cell E x (homF catF (g₂ ∘ g₁)) (homF catF h) (homF catF i₂))
          (respect_comp catF f₂ f₁)
          (twoF (comp₂ (two_cell D) v u)))
      = comp₂ (two_cell E) (twoF v) (twoF u)
  set_option unifier.max_steps 20000

  structure dbl_functor (D E : Dbl_precat) :=
    (catF : functor (cat D) (cat E))
    (twoF : Π ⦃a b c d : cat D⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
      two_cell D f g h i → two_cell E (catF f) (catF g) (catF h) (catF i))
    (respect_id₁ : respect_id₁_type D E catF twoF)
    (respect_comp₁ : respect_comp₁_type D E catF twoF)
    (respect_id₂ : respect_id₂_type D E catF twoF)
    (respect_comp₂ : respect_comp₂_type D E catF twoF)

end dbl_precat




exit
  (obF : C → D)
  (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b))
  (respect_id : Π (a : C), homF (ID a) = ID (obF a))
  (respect_comp : Π {a b c : C} (g : hom b c) (f : hom a b),
    homF (g ∘ f) = homF g ∘ homF f)
