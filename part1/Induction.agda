module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

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
+-comm′ m zero rewrite +-identity′ m = refl
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

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-sucʳ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-sucʳ zero n = refl
*-sucʳ (suc m) n
  rewrite +-suc m (suc m * n)
        | *-sucʳ m n
        | sym (+-assoc n m (m * n))
        | sym (+-assoc m n (m * n))
        | +-comm m n
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zeroʳ m = refl
*-comm m (suc n)
  rewrite *-sucʳ m n
        | *-comm m n
  = refl

∸-zeroʳ : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zeroʳ zero = refl
∸-zeroʳ (suc n) = refl

∸-suc : ∀ (m n : ℕ) → m ∸ suc n ≡ m ∸ n ∸ 1
∸-suc zero n
  rewrite ∸-zeroʳ n
        | ∸-zeroʳ 1
  = refl
∸-suc (suc m) zero = refl
∸-suc (suc m) (suc n) rewrite ∸-suc m n = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m n zero rewrite +-identityʳ n = refl
∸-|-assoc m n (suc p)
  rewrite +-suc n p
        | ∸-suc (m ∸ n) p
        | ∸-suc m (n + p)
        | ∸-|-assoc m n p
  = refl

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p
  rewrite ^-distribˡ-|-* m n p
        | *-assoc m (m ^ n) (m ^ p)
  = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p
        | *-assoc m (m ^ p) (n * (n ^ p))
        | *-assoc m n (m ^ p * (n ^ p))
        | sym (*-assoc n (m ^ p) (n ^ p))
        | sym (*-assoc (m ^ p) n (n ^ p))
        | *-comm n (m ^ p)
  = refl

^-oneʳ : ∀ (n : ℕ) → 1 ^ n ≡ 1
^-oneʳ zero = refl
^-oneʳ (suc n)
  rewrite +-identityʳ (1 ^ n)
        | ^-oneʳ n
  = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p rewrite ^-oneʳ p = refl
^-*-assoc m (suc n) p
  rewrite ^-distribʳ-* m (m ^ n) p
        | ^-distribˡ-|-* m p (n * p)
        | ^-*-assoc m n p
  = refl
