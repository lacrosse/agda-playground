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

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (bin O) = bin I
inc (bin I) = (inc bin) O

_ = inc (⟨⟩ I O I I) ≡⟨⟩ ⟨⟩ I I O O ∎
_ = inc (⟨⟩ I O I O) ≡⟨⟩ ⟨⟩ I O I I ∎
_ = inc (⟨⟩ I I I I) ≡⟨⟩ ⟨⟩ I O O O O ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ = to 1 ≡⟨⟩ ⟨⟩ I ∎
_ = to 93 ≡⟨⟩ ⟨⟩ I O I I I O I ∎

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = 2 * from bin
from (bin I) = 2 * from bin + 1

_ = from (⟨⟩ O O O O) ≡⟨⟩ 0 ∎
_ = from (⟨⟩ I O I I I O I) ≡⟨⟩ 93 ∎
