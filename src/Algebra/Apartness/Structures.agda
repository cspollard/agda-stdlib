------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic structures with an apartness relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Apartness.Structures where

open import Algebra.Core using (Op₁; Op₂)
open import Relation.Binary.Core using (Rel)
open import Level using (_⊔_; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₂)
open import Algebra.Definitions using (Invertible)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.Structures using (IsEquivalence; IsApartnessRelation; IsTotalOrder)
open import Relation.Binary.Definitions using (Tight)
open import Relation.Nullary using (¬_)
import Relation.Binary.Properties.ApartnessRelation as ApartnessRelation

private
  Iso : ∀ {a b} → Set a → Set b → Set _
  Iso A B = (A → B) × (B → A)

record IsHeytingCommutativeRing
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isCommutativeRing   : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
    isApartnessRelation : IsApartnessRelation _≈_ _#_

  open IsCommutativeRing isCommutativeRing public
    renaming (refl to ≈-refl; reflexive to ≈-reflexive)

  open IsApartnessRelation isApartnessRelation public

  field
    #⇔invertible : ∀ {x y} → Iso (x # y) (Invertible _≈_ 1# _*_ (x - y))

  ¬#-isEquivalence : IsEquivalence _¬#_
  ¬#-isEquivalence = ApartnessRelation.¬#-isEquivalence ≈-refl isApartnessRelation


record IsHeytingField
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isHeytingCommutativeRing : IsHeytingCommutativeRing _≈_ _#_ _+_ _*_ -_ 0# 1#
    tight                    : Tight _≈_ _#_

  open IsHeytingCommutativeRing isHeytingCommutativeRing public


record IsOrderedField
  {c ℓ₁ ℓ₂ ℓ₃} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_≤_ : Rel Carrier ℓ₃)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where

  field
    isHeytingField : IsHeytingField _≈_ _#_ _+_ _*_ -_ 0# 1#

  open IsHeytingField isHeytingField public

  field
    isTotalOrder : IsTotalOrder _¬#_ _≤_
    a≤b→a+c≤b+c : ∀ {a b} c → a ≤ b → (a + c) ≤ (b + c)
    0≤a→0≤b→0≤a*b : ∀ {a b} → 0# ≤ a → 0# ≤ b → 0# ≤ (a * b)

  open IsTotalOrder isTotalOrder public
    renaming (refl to ¬#-refl; reflexive to ¬#-reflexive)



open import Relation.Unary using (Pred; _⊆_)


module _ {a r p} {A : Set a} (_≤_ : Rel A r) (P : Pred A p) where
  UpperBound : A → Set _
  UpperBound q = ∀ x → P x → x ≤ q

  Least : A → Set _
  Least q = P q × (∀ x → P x → q ≤ x)

module _ {a r p} {A : Set a} (_≤_ : Rel A r) (P : Pred A p) where
  Supremum : A → Set _
  Supremum = Least _≤_ (UpperBound _≤_ P)



open import Level using (Level)
DedekindComplete : ∀ {c r} {C : Set c} (_≤_ : Rel C r) → (p : Level) → Set _
DedekindComplete {C = C} _≤_ p = ∀ (P : Pred C p) → ∃[ q ] Supremum _≤_ P q


record IsRealField
  {c ℓ₁ ℓ₂ ℓ₃ p}
  {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_≤_ : Rel Carrier ℓ₃)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ suc p) where

  field
    isOrderedField : IsOrderedField _≈_ _#_ _≤_ _+_ _*_ -_ 0# 1#

  open IsOrderedField isOrderedField public

  field
    dedekind-complete : DedekindComplete _≤_ p
