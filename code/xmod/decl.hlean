import algebra.groupoid algebra.group

open iso eq category is_trunc path_algebra
attribute comp [reducible]

structure xmod_aux [class] {P₀ : Type} [P : groupoid P₀] (M : P₀ → Group) : Type :=
  (P₀_hset : is_hset P₀)
  (μ : Π ⦃p : P₀⦄, M p → hom p p)
  (μ_respect_comp : Π ⦃p : P₀⦄ (b a : M p), μ (b * a) = μ b ∘ μ a)
  (μ_respect_id : Π (p : P₀), μ 1 = ID p)

structure xmod [class] {P₀ : Type} [P : groupoid P₀] (M : P₀ → Group)
  extends xmod_aux M :=
  (φ : Π ⦃p q : P₀⦄, hom p q → M p → M q)
  (φ_respect_id : Π ⦃p : P₀⦄ (x : M p), φ (ID p) x = x)
  (φ_respect_P_comp : Π ⦃p q r : P₀⦄ (b : hom q r) (a : hom p q) (x : M p),
    φ (b ∘ a) x = φ b (φ a x))
  (φ_respect_M_comp : Π ⦃p q : P₀⦄ (a : hom p q) (y x : M p),
    φ a (y * x) = (φ a y) * (φ a x))
  (CM1 : Π ⦃p q : P₀⦄ (a : hom p q) (x : M p), μ (φ a x) = a ∘ (μ x) ∘ (a⁻¹))
  (CM2 : Π ⦃p : P₀⦄ (c x : M p), φ (μ c) x = c * (x * (@has_inv.inv (M p) _ c)))

structure Xmod : Type :=
  (carrier : Type)
  (gpd : groupoid carrier)
  (groups : carrier → Group)
  (struct : @xmod carrier gpd groups)

attribute Xmod.struct [instance]
attribute Xmod.gpd [instance]
attribute Xmod.carrier [coercion]

--Some really basic facts
namespace xmod
  variables {P₀ : Type} [P : groupoid P₀] (M : P₀ → Group)
  variable [MM : xmod M]
  include P MM

  definition μ_respect_inv ⦃p : P₀⦄ (a : M p) : μ P (has_inv.inv a) = (μ P a)⁻¹ :=
  begin
    assert H : (@μ P₀ P M MM p (has_inv.inv a)) ∘ (μ P a) = ((μ P a)⁻¹) ∘ (μ P a),
      apply concat, apply eq.inverse, apply μ_respect_comp,
      apply concat, apply (ap (λ x, μ P x)), apply mul_left_inv,
      apply concat, apply μ_respect_id,
      apply eq.inverse, apply left_inverse,
    apply epi.elim, exact H,
  end

  definition φ_respect_one ⦃p q : P₀⦄ (a : hom p q) : @φ P₀ P M MM p q a 1 = 1 :=
  begin
    assert H : @φ P₀ P M MM p q a 1 * 1 = (@φ P₀ P M MM p q a 1) * (@φ P₀ P M MM p q a 1),
      apply eq.inverse, apply concat, apply eq.inverse, apply φ_respect_M_comp,
      apply concat, apply (ap (λ x, φ a x)), apply one_mul,
      apply eq.inverse, apply mul_one,
    apply eq.inverse, apply (mul_left_cancel H),
  end

end xmod
