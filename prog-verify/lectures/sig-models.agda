module sig-models where

open import Data.String using (String)
open import Data.Bool
open import Data.Maybe
open import Data.Nat

record Constant {SetOfSorts : Set} (Sort : SetOfSorts) : Set where
  constructor const
  field
    name : String

-- purely syntax
data Signature (SetOfSorts : Set) : Set where
  constant : {Sort : SetOfSorts} → Constant Sort → Signature SetOfSorts
  -- fn2 : {A B C : SetOfSorts}
  combine : Signature SetOfSorts → Signature SetOfSorts → Signature SetOfSorts

record PartialModel {SetOfSorts : Set} (sig : Signature SetOfSorts) : Set₁ where
  field
    ⌊_⌋ : SetOfSorts → Set
    constants : {Sort : SetOfSorts} → Constant Sort → Maybe ⌊ Sort ⌋

-- record TotalModel {SetOfSorts : Set} (sig : Signature SetOfSorts) : Set₁ where
--   field
--     ⌊_⌋ : SetOfSorts → Set
--     constants : {Sort : SetOfSorts} → Constant Sort → ⌊ Sort ⌋

record Theory (SetOfSorts : Set) : Set₁ where
  field
    sig : Signature SetOfSorts
    -- {Int, 0, 1, +}
    interpreted : PartialModel sig  -- <--- a partial model aka the partial bits can be filled in arbtrarily therefore it's actually a set of models
    -- Int -> Int

-- instantiateEverything : PartialModel sig → List (TotalModel sig)


data Pressburger : Set where
  Nat : Pressburger

pressburger-syn : Signature Pressburger
pressburger-syn = combine (combine
  (constant {Sort = Nat} (const "0"))
  (constant {Sort = Nat} (const "1")))
  (constant {Sort = Nat} (const "x"))

open Theory

pressburger-sig : Theory Pressburger
sig pressburger-sig = pressburger-syn
PartialModel.⌊ interpreted pressburger-sig ⌋ Nat = ℕ
PartialModel.constants (interpreted pressburger-sig) {Nat} (const "0") = just 0
PartialModel.constants (interpreted pressburger-sig) {Nat} (const "1") = just 1
PartialModel.constants (interpreted pressburger-sig) {Nat} (const _) = nothing

data Sat {SetOfSorts : Set} (sig : Signature SetOfSorts) : Set₁ where
  sat : PartialModel sig → Sat sig
  unsat : Sat sig

