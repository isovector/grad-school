open import Data.Nat

module background (V : Set) where
  open import Data.Bool as 𝔹
    using (Bool; true; false; not)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  import Relation.Nullary as Type
  open import Data.Empty using (⊥-elim)

  data Formula : Set where
    var     : V → Formula
    ⊤ ⊥     : Formula
    ¬_      : Formula → Formula
    _∧_ _∨_ : Formula → Formula → Formula

  infixr 10 ¬_
  infixl 6 _∨_
  infixl 5 _∧_

  Model : Set
  Model = V → Maybe Bool

  private variable
    M : Model
    A B C : Formula
    p : V

  _⊭_ : Model → Formula → Set

  {-# NO_POSITIVITY_CHECK #-}
  data _⊨_ (M : Model) : Formula → Set where
    ⊨-lookup : M p ≡ just true → M ⊨ var p
    ⊨-⊤      :                   M ⊨ ⊤
    ⊨-¬      : M ⊭ A           → M ⊨ ¬ A
    ⊨-∧      : M ⊨ A           → M ⊨ B → M ⊨ A ∧ B
    ⊨-inl    : M ⊨ A           → M ⊨ A ∨ B
    ⊨-inr    : M ⊨ B           → M ⊨ A ∨ B
  infix 4 _⊨_

  M ⊭ A = Type.¬ (M ⊨ A)
  infix 4 _⊭_

--   postulate
--     ⊭-¬ : M ⊭ ¬ A → M ⊨ A

  Valid : Formula → Set
  Valid A = ∀ M → M ⊨ A

  Satisfiable : Formula → Set
  Satisfiable A = Σ Model λ M → M ⊨ A

  Unsatisfiable : Formula → Set
  Unsatisfiable A = Valid (¬ A)

  _Entails_ : Formula → Formula → Set
  A Entails B = ∀ M → M ⊨ A → M ⊨ B

  _≣_ : Formula → Formula → Set
  A ≣ B = A Entails B × B Entails A

  infixl 4 _≣_

  ∧¬ : A ∧ ¬ A ≣ ⊥
  proj₁ ∧¬ M (⊨-∧ x (⊨-¬ x₁)) = ⊥-elim (x₁ x)
  proj₂ ∧¬ M ()

  ¬¬-elim : ¬ ¬ A ≣ A
  proj₁ ¬¬-elim M (⊨-¬ x) = ?
  proj₂ ¬¬-elim M x       = ⊨-¬ λ { (⊨-¬ y) → y x }

  ∧⊥≣⊥ : A ∧ ⊥ ≣ ⊥
  proj₁ ∧⊥≣⊥ M (⊨-∧ x ())
  proj₂ ∧⊥≣⊥ M ()

  ∧-distribʳ-∨ : (A ∨ B) ∧ C ≣ (A ∧ C) ∨ (B ∧ C)
  proj₁ ∧-distribʳ-∨ M (⊨-∧ (⊨-inl x) y) = ⊨-inl (⊨-∧ x y)
  proj₁ ∧-distribʳ-∨ M (⊨-∧ (⊨-inr x) y) = ⊨-inr (⊨-∧ x y)
  proj₂ ∧-distribʳ-∨ M (⊨-inl (⊨-∧ x y)) = ⊨-∧ (⊨-inl x) y
  proj₂ ∧-distribʳ-∨ M (⊨-inr (⊨-∧ x y)) = ⊨-∧ (⊨-inr x) y

  ¬-distrib-∧ : ¬ (A ∧ B) ≣ ¬ A ∨ ¬ B
  proj₁ ¬-distrib-∧ M (⊨-¬ x) = {! !}
  proj₂ ¬-distrib-∧ M (⊨-inl x) = ⊨-¬ λ { (⊨-∧ x₁ x₂) → {! !} }
  proj₂ ¬-distrib-∧ M (⊨-inr x) = ⊨-¬ λ { (⊨-∧ x₁ x₂) → {! !} }

-- --   ⌈_⌋ : Formula → (V → Maybe Bool)



