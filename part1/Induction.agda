module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩ 7 + 5
  ≡⟨⟩ 12
  ≡⟨⟩ 3 + 9
  ≡⟨⟩ 3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin (zero + n) + p
  ≡⟨⟩   n + p
  ≡⟨⟩   zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin (suc m + n) + p
  ≡⟨⟩   suc (m + n) + p
  ≡⟨⟩   suc (m + n + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
  ≡⟨⟩   suc m + (n + p)
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = begin zero + zero ≡⟨⟩ zero ∎
+-identityʳ (suc m) =
  begin (suc m) + zero
  ≡⟨⟩   suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
  ∎

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin zero + suc n
  ≡⟨⟩   suc n
  ∎
+-suc (suc m) n =
  begin suc m + suc n
  ≡⟨⟩   suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
  ≡⟨⟩   suc (suc m + n)
  ∎

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin m + zero
  ≡⟨ +-identityʳ m ⟩
        m
  ≡⟨⟩ zero + m
  ∎
+-comm m (suc n) =
  begin m + suc n
  ≡⟨ +-suc m n ⟩
        suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
  ≡⟨⟩   suc n + m
  ∎

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero
  rewrite +-identity′ m
  = refl
+-comm′ m (suc n)
  rewrite +-suc′ m n
        | +-comm′ m n
  = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
        m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
        m + (n + p + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
        m + (n + p) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite +-comm m (n + p)
        | +-assoc n p m
        | +-comm p m
  = refl

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m zero p
  rewrite *-zeroʳ p
        | +-identityʳ m
        | +-identityʳ (m * p)
  = refl
*-distrib-+ m (suc n) p
  rewrite +-suc m n
        | *-distrib-+ m n p
        | +-swap p (m * p) (n * p)
  = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
        | *-assoc m n p
  = refl
