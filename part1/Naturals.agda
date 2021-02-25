module part1.Naturals where

data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩ (suc 2) + 4
  ≡⟨⟩ suc (2 + 4)
  ≡⟨⟩ suc ((suc 1) + 4)
  ≡⟨⟩ suc (suc (1 + 4))
  ≡⟨⟩ suc (suc ((suc 0) + 4))
  ≡⟨⟩ suc (suc (suc (0 + 4)))
  ≡⟨⟩ suc (suc (suc 4))
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩ 3 + (1 * 3)
  ≡⟨⟩ 3 + (3 + (0 * 3))
  ≡⟨⟩ 3 + (3 + 0)
  ≡⟨⟩ 6
  ∎

-- *-example
_ =
  begin 3 * 4
  ≡⟨⟩ 4 + (2 * 4)
  ≡⟨⟩ 4 + (4 + (1 * 4))
  ≡⟨⟩ 4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩ 4 + (4 + (4 + 0))
  ≡⟨⟩ 12
  ∎

-- _^_
_^_ : ℕ → ℕ → ℕ
m ^ zero    = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩ 3 * (3 ^ 3)
  ≡⟨⟩ 3 * (3 * (3 ^ 2))
  ≡⟨⟩ 3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩ 3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩ 3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩ 81
  ∎

-- monus
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩ 2 ∸ 1
  ≡⟨⟩ 1 ∸ 0
  ≡⟨⟩ 1
  ∎

-- ∸-example_1
_ =
  begin
    5 ∸ 3
  ≡⟨⟩ 4 ∸ 2
  ≡⟨⟩ 3 ∸ 1
  ≡⟨⟩ 2 ∸ 0
  ≡⟨⟩ 2
  ∎

-- ∸-example_2
_ =
  begin
    3 ∸ 5
  ≡⟨⟩ 2 ∸ 4
  ≡⟨⟩ 1 ∸ 3
  ≡⟨⟩ 0 ∸ 2
  ≡⟨⟩ 0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Bin
-- exported
