import algebra.precategory.basic
open category is_trunc eq sigma sigma.ops unit

structure worm_precat {D₀ : Type} (C  : precategory D₀)
    (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type) :=
  (comp₁ : proof Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄
    ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄,
    (D₂ g₁ g₂ h₂ i₂) → (D₂ f₁ g₁ h₁ i₁) → (@D₂ a b c₂ d₂ f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁)) qed)
  (ID₁ : proof Π ⦃a b : D₀⦄ (f : hom a b), D₂ f f (ID a) (ID b) qed)
  (assoc₁ : proof Π ⦃a b c₁ d₁ c₂ d₂ c₃ d₃ : D₀⦄
    ⦃f  : hom a b⦄   ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄
    ⦃g₃ : hom c₃ d₃⦄ ⦃h₃ : hom c₂ c₃⦄ ⦃i₃ : hom d₂ d₃⦄
    (w : D₂ g₂ g₃ h₃ i₃) (v : D₂ g₁ g₂ h₂ i₂) (u : D₂ f g₁ h₁ i₁),
    (assoc i₃ i₂ i₁) ▹ ((assoc h₃ h₂ h₁) ▹
        (comp₁ w (comp₁ v u))) = (comp₁ (comp₁ w v) u) qed)
  (id_left₁ : proof Π ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i),
    (id_left i) ▹ ((id_left h) ▹
        (comp₁ (ID₁ g) u)) = u qed)
  (id_right₁ : proof Π ⦃a b c d : D₀⦄
    ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄
    (u : D₂ f g h i),
    (id_right i) ▹ ((id_right h) ▹
        (comp₁ u (ID₁ f))) = u qed)
  (homH' : proof Π ⦃a b c d : D₀⦄ ⦃f : hom a b⦄ ⦃g : hom c d⦄ ⦃h : hom a c⦄ ⦃i : hom b d⦄,
    is_hset (D₂ f g h i) qed)

structure dbl_precat {D₀ : Type} (C : precategory D₀)
  (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d),
    Type)
  extends worm_precat C D₂,
    worm_precat C (λ ⦃a b c d : D₀⦄ f g h i, D₂ h i f g)
  renaming comp₁→comp₂ ID₁→ID₂ assoc₁→assoc₂
    id_left₁→id_left₂ id_right₁→id_right₂ homH'→homH'_dontuse :=
  (id_comp₁ : proof Π {a b c : D₀} (f : hom a b) (g : hom b c),
    ID₂ (g ∘ f) = comp₁ (ID₂ g) (ID₂ f) qed)
  (id_comp₂ : proof Π {a b c : D₀} (f : hom a b) (g : hom b c),
    ID₁ (g ∘ f) = comp₂ (ID₁ g) (ID₁ f) qed)
  (zero_unique : proof Π (a : D₀), ID₁ (ID a) = ID₂ (ID a) qed)
  (interchange : proof Π {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : D₀}
    {f₀₀ : hom a₀₀ a₀₁} {f₀₁ : hom a₀₁ a₀₂} {f₁₀ : hom a₁₀ a₁₁}
    {f₁₁ : hom a₁₁ a₁₂} {f₂₀ : hom a₂₀ a₂₁} {f₂₁ : hom a₂₁ a₂₂}
    {g₀₀ : hom a₀₀ a₁₀} {g₀₁ : hom a₀₁ a₁₁} {g₀₂ : hom a₀₂ a₁₂}
    {g₁₀ : hom a₁₀ a₂₀} {g₁₁ : hom a₁₁ a₂₁} {g₁₂ : hom a₁₂ a₂₂}
    (x : D₂ f₁₁ f₂₁ g₁₁ g₁₂) (w : D₂ f₁₀ f₂₀ g₁₀ g₁₁)
    (v : D₂ f₀₁ f₁₁ g₀₁ g₀₂) (u : D₂ f₀₀ f₁₀ g₀₀ g₀₁),
    comp₁ (comp₂ x w) (comp₂ v u) = comp₂ (comp₁ x v) (comp₁ w u) qed)

structure Dbl_precat : Type :=
  (cat : Precategory)
  (two_cell : Π ⦃a b c d : cat⦄ (f : hom a b)
    (g : hom c d) (h : hom a c) (i : hom b d), Type)
  (struct : dbl_precat cat two_cell)
  (obj_set : is_hset (carrier cat))
