open import Data.Nat

module background (V : Set) where
  open import Agda.Primitive

  open import Data.Bool
    using (Bool; true; false; not)
    renaming (_∧_ to and; _∨_ to or)
  open import Data.Maybe using (Maybe; just; ap; nothing)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product hiding (_<*>_; map)
  import Relation.Nullary as Type
  open import Data.Empty using (⊥-elim)
  open import Function using (const; id; _∘_)

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

  module _ where
    pure : ∀ {a} {A : Set a} → A → Maybe A
    pure = just

    _<*>_ = ap

    ⌜_⌟ : Formula → Model → Maybe Bool
    ⌜ var x ⌟ M = M x
    ⌜ ⊤ ⌟ M     = (| true |)
    ⌜ ⊥ ⌟ M     = (| false |)
    ⌜ ¬ x ⌟ M   = (| not (⌜ x ⌟ M) |)
    ⌜ x ∧ y ⌟ M = (| and (⌜ x ⌟ M) (⌜ y ⌟ M) |)
    ⌜ x ∨ y ⌟ M = (| or  (⌜ x ⌟ M) (⌜ y ⌟ M) |)


  private variable
    M : Model
    A B C : Formula
    p : V


  _⊨_ : Model →  Formula → Set
  M ⊨ A = ⌜ A ⌟ M ≡ just true
  infix 4 _⊨_ _⊭_

  _⊭_ : Model → Formula → Set
  M ⊭ A = ⌜ A ⌟ M ≡ just false

  Valid : Formula → Set
  Valid A = ∀ M → M ⊨ A

  Satisfiable : Formula → Set
  Satisfiable A = Σ Model λ M → M ⊨ A

  Unsatisfiable : Formula → Set
  Unsatisfiable A = Valid (¬ A)

  _Entails_ : Formula → Formula → Set
  A Entails B = ∀ M → M ⊨ A → M ⊨ B

  _≣_ : Formula → Formula → Set
  A ≣ B = ∀ M → (M ⊨ A → M ⊨ B) × (M ⊨ B → M ⊨ A)

  infixl 4 _≣_

  ≣-refl : A ≣ A
  proj₁ (≣-refl M) = id
  proj₂ (≣-refl M) = id

  ≣-sym : A ≣ B → B ≣ A
  ≣-sym x M with x M
  ... | fst , snd = snd , fst

  ≣-trans : A ≣ B → B ≣ C → A ≣ C
  ≣-trans A≣B B≣C M with A≣B M | B≣C M
  ... | ab₁ , ab₂ | bc₁ , bc₂ = bc₁ ∘ ab₁ , ab₂ ∘ bc₂

  open import Relation.Binary

  ≣-equiv : IsEquivalence _≣_
  IsEquivalence.refl  ≣-equiv {A} = ≣-refl {A}
  IsEquivalence.sym   ≣-equiv {A} {B} = ≣-sym {A} {B}
  IsEquivalence.trans ≣-equiv {A} {B} {C} = ≣-trans {A} {B} {C}

  ≣-setoid : Setoid lzero lzero
  Setoid.Carrier ≣-setoid = Formula
  Setoid._≈_ ≣-setoid = _≣_
  Setoid.isEquivalence ≣-setoid = ≣-equiv

  open import Relation.Binary.Reasoning.Setoid (≣-setoid)

  ∧¬ : A ∧ ¬ A ≣ ⊥
  ∧¬ {A} M with ⌜ A ⌟ M
  ... | just false = id , id
  ... | just true = id , id
  ... | nothing = (λ ()) , λ ()

  ¬¬-elim : ¬ ¬ A ≣ A
  ¬¬-elim {A} M with ⌜ A ⌟ M
  ... | just false = id , id
  ... | just true = id , id
  ... | nothing = (λ ()) , λ ()

  ∧-comm : A ∧ B ≣ B ∧ A
  proj₁ (∧-comm {A} {B} M) x = {! !}
  proj₂ (∧-comm {A} {B} M) x = {! !}



