module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; *-zeroʳ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
    → zero ≤ n
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s h1) (s≤s h2) = s≤s (≤-trans h1 h2)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s h1) (s≤s h2) = cong suc (≤-antisym h1 h2)

data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
    → Total m n

  flipped :
      n ≤ m
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero _ = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) = with-s≤s (≤-total m n)
  where with-s≤s : Total m n → Total (suc m) (suc n)
        with-s≤s (forward h) = forward (s≤s h)
        with-s≤s (flipped h) = flipped (s≤s h)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q h = h
+-monoʳ-≤ (suc n) p q h = s≤s (+-monoʳ-≤ n p q h)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ n m p h
  rewrite +-comm m p
        | +-comm n p
  = +-monoʳ-≤ p n m h

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q h1 h2 = ≤-trans (+-monoˡ-≤ m n p h1) (+-monoʳ-≤ n p q h2)

*-monoʳ-≤ : ∀ (m n p : ℕ) → n ≤ p → m * n ≤ m * p
*-monoʳ-≤ zero n p h = z≤n
*-monoʳ-≤ (suc m) n p h = +-mono-≤ n p (m * n) (m * p) h (*-monoʳ-≤ m n p h)

*-monoˡ-≤ : ∀ (m n p : ℕ) → n ≤ p → n * m ≤ p * m
*-monoˡ-≤ zero n p h
  rewrite *-zeroʳ n
        | *-zeroʳ p
  = z≤n
*-monoˡ-≤ (suc m) n p h
  rewrite *-comm n (suc m)
        | *-comm p (suc m)
  = +-mono-≤ n p (m * n) (m * p) h (*-monoʳ-≤ m n p h)

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q h1 h2 = ≤-trans (*-monoʳ-≤ m p q h2) (*-monoˡ-≤ q m n h1)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  0<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans 0<s (s<s h) = 0<s
<-trans (s<s h1) (s<s h2) = s<s (<-trans h1 h2)

_>_ : ℕ → ℕ → Set
m > n = n < m

data Trichotomy (m n : ℕ) : Set where
  forward  : m < n → Trichotomy m n
  equal    : m ≡ n → Trichotomy m n
  backward : m > n → Trichotomy m n

+-monoʳ-< : ∀ (m n p : ℕ) → n < p → m + n < m + p
+-monoʳ-< zero n p h = h
+-monoʳ-< (suc m) n p h = s<s (+-monoʳ-< m n p h)

+-monoˡ-< : ∀ (m n p : ℕ) → n < p → n + m < p + m
+-monoˡ-< zero n p h
  rewrite +-identityʳ n
        | +-identityʳ p
  = h
+-monoˡ-< (suc m) n p h
  rewrite +-comm n (suc m)
        | +-comm p (suc m)
  = s<s (+-monoʳ-< m n p h)

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q h1 h2 = <-trans (+-monoʳ-< _ _ _ h2) (+-monoˡ-< _ _ _ h1)

≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero (suc n) (s≤s h) = 0<s
≤-iff-< (suc _) (suc _) (s≤s h) = s<s (≤-iff-< _ _ h)

<-iff-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-iff-≤ zero (suc n) 0<s = s≤s z≤n
<-iff-≤ (suc m) (suc n) (s<s h) = s≤s (<-iff-≤ _ _ h)

<-≤ : ∀ (m n : ℕ) → m < n → m ≤ n
<-≤ zero (suc n) 0<s = z≤n
<-≤ (suc m) (suc n) (s<s h) = s≤s (<-≤ _ _ h)

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited h1 h2 = ≤-iff-< _ _ (≤-trans (s≤s (<-≤ _ _ h1)) (<-iff-≤ _ _ h2))

data even : ℕ → Set
data odd  : ℕ → Set
data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd  n → even (suc n)
data odd where
  suc  : ∀ {n : ℕ} → even n → odd  (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)

o+e≡o : ∀ {m n : ℕ} → odd  m → even n → odd  (m + n)

e+e≡e zero    en = en
e+e≡e (suc o) en = suc (o+e≡o o en)

o+e≡o (suc e) en = suc (e+e≡e e en)
