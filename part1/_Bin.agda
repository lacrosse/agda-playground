module part1._Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _*_)

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
from (bin I) = suc (2 * from bin)

_ = from (⟨⟩ O O O O) ≡⟨⟩ 0 ∎
_ = from (⟨⟩ I O I I I O I) ≡⟨⟩ 93 ∎
