module 01-naturals where

-- https://plfa.github.io/Naturals/

-- Natural numbers (aka 'Peano numbers') are defined inductively. There
-- is an assumtion, zero is a ℕ, and an inductive case, that given a
-- ℕ we can form a new ℕ, its successor.

-- The type of ℕ is itself Set - this makes sense, as it is a (possibly
-- infinite) set of values built from some known cases. 
data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

-- We can tell Agda that the ℕ type can be treated as a builtin natural
-- type, allowing it to be lowered to a hardware bigint rather than a
-- linked list of constructors.
{-# BUILTIN NATURAL ℕ #-}