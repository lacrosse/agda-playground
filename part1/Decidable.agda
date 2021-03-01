module part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import part1.Relations using (_<_; 0<s; s<s)
open import part1.Isomorphism using (_⇔_)

-- Evidence vs computation

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ _     = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- Relating evidence and computation

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    _       tt = z≤n
≤ᵇ→≤ (suc m) (suc n) t  = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n     = tt
≤→≤ᵇ (s≤s t) = ≤→≤ᵇ t

-- The best of both

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes  m≤n = yes (s≤s m≤n)
... | no  ¬m≤n = no (¬s≤s ¬m≤n)

-- Exercises

¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
_     <? zero  = no ¬n<z
zero  <? suc n = yes 0<s
suc m <? suc n with m <? n
... | yes m<n  = yes (s<s m<n)
... | no  ¬m<n = no (¬s<s ¬m<n)

-- _≡ℕ?_

z≢s : ∀ {n : ℕ} → suc n ≢ zero
z≢s ()

s≢z : ∀ {n : ℕ} → zero ≢ suc n
s≢z ()

s≢s : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n
s≢s m≢n refl = m≢n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
suc m ≡ℕ? zero = no z≢s
zero ≡ℕ? suc n = no s≢z
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes m≡n  = yes (cong suc m≡n)
... | no  ¬m≡n = no  (s≢s ¬m≡n)

-- Decidables ⇔ booleans

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
... | true  | b→≤ | _   = yes (b→≤ tt)
... | false | g   | ≤→b = no ≤→b

-- Erasure

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no  x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋

to-witness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
to-witness {_} {yes x} _ = x

from-witness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
from-witness {_} {yes _} _ = tt
from-witness {_} {no ¬a} a = ¬a a

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = to-witness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = from-witness

-- Logical connectives

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b  = b
false ∧ _  = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×-dec yes b = yes ⟨ a , b ⟩
no ¬a ×-dec _     = no λ{⟨ a , _ ⟩ → ¬a a}
_     ×-dec no ¬b = no λ{⟨ _ , b ⟩ → ¬b b}

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
false ∨ false = false
false ∨ true  = true
true  ∨ _     = true

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
no ¬a ⊎-dec no ¬b = no λ{(inj₁ a) → ¬a a ; (inj₂ b) → ¬b b}
yes a ⊎-dec _     = yes (inj₁ a)
_     ⊎-dec yes b = yes (inj₂ b)

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes a)  = no (λ ¬a → ¬a a)
¬? (no  ¬a) = yes ¬a

_⊃_ : Bool → Bool → Bool
true  ⊃ false = false
false ⊃ _     = true
_     ⊃ true  = true

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
yes a →-dec no ¬b = no  λ a→b → ¬b (a→b a)
no ¬a →-dec _     = yes λ a   → ⊥-elim (¬a a)
_     →-dec yes b = yes λ _   → b
