{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Algebra.Structures.Ordered
  {a ℓ o} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  (_≤_ : Rel A o)    -- The order relation
  where


open import Algebra.Core using (Op₂; Op₁)
open import Algebra.Structures _≈_ using (IsField)
import Relation.Binary.Structures _≈_ as RB using (IsTotalOrder)
open import Relation.Binary using (_⇔_)
open import Level using (_⊔_)
open import Data.Product using (_×_)


record IsOrderedField
  (+ * : Op₂ A) (- 1/ : Op₁ A) (0# 1# : A)
  : Set (a ⊔ ℓ ⊔ o) where

  field 
    isField : IsField + * - 1/ 0# 1#
    isTotalOrder : RB.IsTotalOrder _≤_
    a≤b⇔a+c≤a+c : (λ a b → a ≤ b) ⇔ (λ a b → ∀ c → + a c ≤ + b c)
    0≤a×0≤b⇔0≤a*b : ∀ a b → 0# ≤ a × 0# ≤ b → 0# ≤ * a b

  open IsField isField public
  open RB.IsTotalOrder isTotalOrder public renaming
    ( refl to ≤-refl
    ; reflexive to ≤-reflexive
    )