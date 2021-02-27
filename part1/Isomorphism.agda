module part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Function composition

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

-- Extensionality

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app-inv : ∀ (m n : ℕ) → m +′ n ≡ n + m
same-app-inv _ zero = refl
same-app-inv m (suc n) = cong suc (same-app-inv m n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = same-app-inv m n

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g
