import algebra.groupoid algebra.group

open groupoid precategory morphism function eq truncation
reducible compose

structure xmod_aux [class] {P₀ : Type} (P : groupoid P₀) (M : groupoid P₀)
  : Type :=
  (P₀_hset : is_hset P₀)
  (μ : Π ⦃p q : P₀⦄, @hom _ M p q → @hom _ P p q)
  (μ_respect_comp : Π ⦃p q r : P₀⦄ (b : @hom _ M q r) (a : @hom _ M p q),
    μ (b ∘ a) = μ b ∘ μ a)
  (μ_respect_id : Π (p : P₀), μ (ID p) = ID p)

structure xmod [class] {P₀ : Type} (P : groupoid P₀) (M : groupoid P₀)
  extends xmod_aux P M :=
  (M_disconnected : Π ⦃p q : P₀⦄, @hom _ M p q → p = q)
  (φ : Π ⦃p q : P₀⦄, @hom _ P p q → @hom _ M p p → @hom _ M q q)
  (φ_respect_id : Π ⦃p : P₀⦄ (x : @hom _ M p p), φ id x = x)
  (φ_respect_P_comp : Π ⦃p q r : P₀⦄ (b : @hom _ P q r) (a : @hom _ P p q) (x : @hom _ M p p),
    φ (b ∘ a) x = φ b (φ a x))
  (φ_respect_M_comp : Π ⦃p q : P₀⦄ (a : @hom _ P p q) (y x : @hom _ M p p),
    φ a (y ∘ x) = (φ a y) ∘ (φ a x))
  (CM1 : Π ⦃p q : P₀⦄ (a : @hom _ P p q) (x : @hom _ M p p),
    μ (φ a x) = a ∘ (μ x) ∘ (a⁻¹))
  (CM2 : Π ⦃p : P₀⦄ (c x : @hom _ M p p), φ (μ c) x = c ∘ x ∘ (c⁻¹))
