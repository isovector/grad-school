open import Data.Nat

module background (V : Set) where
  open import Agda.Primitive
  open import Data.Bool
    using (Bool; true; false; not)
    renaming (_∧_ to and; _∨_ to or)
  open import Data.Maybe
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



