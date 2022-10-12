module 02-induction where

-- https://plfa.github.io/Induction/

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- Associativity is the property than an operator works irrespective
-- of order-of-operation. This means that (α ∘ β) ∘ γ ≡ α ∘ (β ∘ γ).

-- Addition has the property of associativity, but this must be proved.
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
    -- This case can also simply be refl, as Agda can infer the
    -- transformations to make.
    begin
        (zero + n) + p
    ≡⟨⟩
        n + p
    ≡⟨⟩
        zero + (n + p)
    ∎
+-assoc (suc m) n p = 
    begin
        (suc m + n) + p
    ≡⟨⟩
        suc (m + n) + p
    ≡⟨⟩
        -- Apply inductive case of + twice to give:
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        -- This case can be reached by applying the +-assoc rule
        -- recursively, but Agda can't figure this out as it is inside
        -- the suc constructor, so an explicit justification must be given.
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎