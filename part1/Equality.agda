module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {X Y Z : Set} {x₁ x₂ : X} {y₁ y₂ : Y} (f : X → Y → Z)
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (f : A → Set) → x ≡ y → f x → f y
subst _ refl h = h

module ≡-Reasoning {A : Set} where
  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin h = h

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ refl = refl

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ h1 ⟩ h2 = trans h1 h2

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl
open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin
  m + zero  ≡⟨ +-identity m ⟩
  m         ≡⟨⟩
  zero + m  ∎
+-comm m (suc n) = begin
  m + suc n    ≡⟨ +-suc m n ⟩
  suc (m + n)  ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)  ≡⟨⟩
  suc n + m    ∎

module ≤-Reasoning where
  data _≤_ : ℕ → ℕ → Set where
    0≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
  infix 4 _≤_

  ≤-refl : ∀ (m : ℕ) → m ≤ m
  ≤-refl zero = 0≤n
  ≤-refl (suc m) = s≤s (≤-refl m)

  ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
  ≤-trans 0≤n _ = 0≤n
  ≤-trans (s≤s h1) (s≤s h2) = s≤s (≤-trans h1 h2)

  infix 1 min_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _max

  min_ : ∀ {m n : ℕ} → m ≤ n → m ≤ n
  min h = h

  _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ} → m ≤ n → m ≤ n
  m ≤⟨⟩ h = h

  _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
  m ≤⟨ h1 ⟩ h2 = ≤-trans h1 h2

  _max : ∀ (m : ℕ) → m ≤ m
  m max = ≤-refl m
open ≤-Reasoning

_ : suc (suc zero) ≤ suc (suc (suc zero))
_ =
  min
    suc (suc zero)
  ≤⟨⟩
    suc (suc zero)
  ≤⟨ s≤s (s≤s 0≤n) ⟩
    suc (suc (suc zero))
  max

-- Rewriting

data even : ℕ → Set
data odd  : ℕ → Set
data even where
  e-z : even zero
  e-s : ∀ {n : ℕ} → odd n → even (suc n)
data odd where
  o-s : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n h rewrite +-comm n m = h

even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n h
  with   m + n  | +-comm m n
...  | .(n + m) | refl       = h

even-comm″ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm″ m n = subst even (+-comm m n)

-- Leibniz/Martin-Löf equality

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (f : A → Set) → f x → f y
