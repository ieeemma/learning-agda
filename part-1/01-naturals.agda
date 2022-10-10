module 01-naturals where

-- https://plfa.github.io/Naturals/

-- Natural numbers (aka 'Peano numbers') are defined inductively. There
-- is an assumption, zero is a ℕ, and an inductive case, that given a
-- ℕ we can form a new ℕ, its successor.
-- The type of ℕ is itself Set - this makes sense, as it is a (possibly
-- infinite) set of values built from some known cases. 
data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

-- We can tell Agda that the ℕ type can be treated as a builtin natural
-- type, allowing it to be lowered to a hardware bigint rather than a
-- linked list of constructors. This also allows typing 0 for zero, 1 for
-- (suc zero), etc.
{-# BUILTIN NATURAL ℕ #-}

-- Addition is an infix function - denoted with two underscores.
-- It is defined inductively. The base case simply states that
-- ∀ α, 0 + α ≡ α. The inductive case encodes the property of
-- commutativity, (1 + α) + β is isomorphic to 1 + (α + β).
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc n) + n′ = suc (n + n′)

-- We can tell Agda that the plus operator has a precedence of 6.
infixl 6 _+_ 

-- Similarly to above, a pragma can be used to tell Agda that this
-- addition operation can be lowered to a hardware int addition.
{-# BUILTIN NATPLUS _+_ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- We can write a proof that 2 + 3 ≡ 5.
-- In Agda, an equality is a type. For the equality to hold, there must
-- be a term of this type, defined below.
_ : 2 + 3 ≡ 5
_ =
    -- Proofs start with the begin_ function, starting with the term
    -- to be transformed (the left-hand-side of the above annotation).
    begin
        2 + 3
    -- The ≡⟨⟩ operator is read 'can be written as'.
    ≡⟨⟩
    -- Applying the inductive case of addition to 2 + 3 gives:
        suc (1 + 3)
    ≡⟨⟩
    -- And a second time:
        suc (suc (0 + 3))
    ≡⟨⟩
    -- Then applying the base case:
        suc (suc 3)
    ≡⟨⟩
    -- Which can be written as:
        5
    -- Proofs end with the QED symbol.
    ∎

-- Agda can often figure this itself, however. For example:
_ : 2 + 3 ≡ 5
_ = refl

-- Monus, like minus, but defined as 0 for any would-be negative results.
_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc m = zero
suc n ∸ suc m = n ∸ m

infixl 6 _∸_
{-# BUILTIN NATMINUS _∸_ #-}

-- Multiplication.
_*_ : ℕ → ℕ → ℕ
n * zero = zero
n * suc m = n + (n * m)

infixl 7 _*_
{-# BUILTIN NATTIMES _*_ #-}

-- Exponentiation.
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n * m)

infixr 8 _^_