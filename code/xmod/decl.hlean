import algebra.groupoid algebra.group

open groupoid precategory morphism function eq truncation path_algebra
reducible compose
coercion [persistent] Group.carrier
instance [persistent] Group.struct

structure xmod_aux [class] {P₀ : Type} (P : groupoid P₀) (M : P₀ → Group) : Type :=
  (P₀_hset : is_hset P₀)
  (μ : Π ⦃p : P₀⦄, M p → hom p p)
  (μ_respect_comp : Π ⦃p : P₀⦄ (b a : M p), μ (b * a) = μ b ∘ μ a)
  (μ_respect_id : Π (p : P₀), μ 1 = ID p)

structure xmod [class] {P₀ : Type} (P : groupoid P₀) (M : P₀ → Group)
  extends xmod_aux P M :=
  (φ : Π ⦃p q : P₀⦄, hom p q → M p → M q)
  (φ_respect_id : Π ⦃p : P₀⦄ (x : M p), φ (ID p) x = x)
  (φ_respect_P_comp : Π ⦃p q r : P₀⦄ (b : hom q r) (a : hom p q) (x : M p),
    φ (b ∘ a) x = φ b (φ a x))
  (φ_respect_M_comp : Π ⦃p q : P₀⦄ (a : hom p q) (y x : M p),
    φ a (y * x) = (φ a y) * (φ a x))
  (CM1 : Π ⦃p q : P₀⦄ (a : hom p q) (x : M p), μ (φ a x) = a ∘ (μ x) ∘ (a⁻¹))
  (CM2 : Π ⦃p : P₀⦄ (c x : M p), φ (μ c) x = c * x * (@group.inv (M p) _ c))
