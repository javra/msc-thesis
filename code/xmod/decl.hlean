import algebra.category.groupoid algebra.group

open iso eq category is_trunc algebra

structure xmod {P₀ : Type} [P : groupoid P₀] (M : P₀ → Group) :=
  (P₀_hset : is_hset P₀)
  (μ : Π ⦃p : P₀⦄, M p → hom p p)
  (μ_respect_comp : Π ⦃p : P₀⦄ (b a : M p), μ (b * a) = μ b ∘ μ a)
  (μ_respect_id : Π (p : P₀), μ 1 = ID p)
  (φ : Π ⦃p q : P₀⦄, hom p q → M p → M q)
  (φ_respect_id : Π ⦃p : P₀⦄ (x : M p), φ (ID p) x = x)
  (φ_respect_P_comp : Π ⦃p q r : P₀⦄ (b : hom q r) (a : hom p q) (x : M p),
    φ (b ∘ a) x = φ b (φ a x))
  (φ_respect_M_comp : Π ⦃p q : P₀⦄ (a : hom p q) (y x : M p),
    φ a (y * x) = (φ a y) * (φ a x))
  (CM1 : Π ⦃p q : P₀⦄ (a : hom p q) (x : M p), μ (φ a x) = a ∘ (μ x) ∘ a⁻¹)
  (CM2 : Π ⦃p : P₀⦄ (c x : M p), φ (μ c) x = c * (x * c⁻¹ᵍ))

structure Xmod :=
  {carrier : Type}
  [gpd : groupoid carrier]
  (groups : carrier → Group)
  (struct : @xmod carrier gpd groups)

attribute Xmod.struct [coercion]
attribute Xmod.gpd [instance]
attribute Xmod.carrier [coercion]

--Some really basic facts
namespace xmod
  variables {P₀ : Type} [P : groupoid P₀] {M : P₀ → Group}
  variable (MM : xmod M)

  definition μ_respect_inv ⦃p : P₀⦄ (a : M p) : μ MM a⁻¹ᵍ = (μ MM a)⁻¹ :=
  begin
    assert H : μ MM a⁻¹ᵍ ∘ μ MM a = (μ MM a)⁻¹ ∘ μ MM a,
      exact calc μ MM a⁻¹ᵍ ∘ μ MM a = μ MM (a⁻¹ᵍ * a) : μ_respect_comp
                               ... = μ MM 1 : by rewrite mul.left_inv
                               ... = id : μ_respect_id
                               ... = (μ MM a)⁻¹ ∘ μ MM a : left_inverse,
    apply epi.elim, exact H,
  end

  definition φ_respect_one ⦃p q : P₀⦄ (a : hom p q) : φ MM a 1 = 1 :=
  begin
    assert H : φ MM a 1 * 1 = φ MM a 1 * φ MM a 1,
      exact calc φ MM a 1 * 1 = φ MM a 1 : mul_one
                          ... = φ MM a (1 * 1)  : one_mul
                          ... = φ MM a 1 * φ MM a 1 : φ_respect_M_comp,
    apply eq.inverse, apply (mul_left_cancel H),
  end

end xmod
