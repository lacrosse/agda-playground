module part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Function composition

open import Function using (_∘_)
-- _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
-- g ∘ f = λ x → g (f x)
-- infixr 1 _∘_

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

-- Isomorphism

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → (from ∘ to) x ≡ x
    to∘from : ∀ (y : B) → (to ∘ from) y ≡ y
open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to = λ x → x
    ; from = λ x → x
    ; from∘to = λ _ → refl
    ; to∘from = λ _ → refl
    }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym i =
  record
    { to = from i
    ; from = to i
    ; from∘to = to∘from i
    ; to∘from = from∘to i
    }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = to B≃C ∘ to A≃B
    ; from = from A≃B ∘ from B≃C
    ; from∘to = λ{x →
        begin
          (from A≃B ∘ from B≃C ∘ to B≃C ∘ to A≃B) x
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          (from A≃B ∘ to A≃B) x
        ≡⟨ (from∘to A≃B) x ⟩
          x
        ∎
      }
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B ∘ from A≃B ∘ from B≃C) y
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          (to B≃C ∘ from B≃C) y
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎
      }
    }

module ≃-Reasoning where
  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin i = i

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl
open ≃-Reasoning

-- Embedding

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → (from ∘ to) x ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to = λ x → x
    ; from = λ x → x
    ; from∘to = λ _ → refl }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to = to B≲C ∘ to A≲B
    ; from = from A≲B ∘ from B≲C
    ; from∘to = λ{x →
        begin
          (from A≲B ∘ from B≲C ∘ to B≲C ∘ to A≲B) x
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          (from A≲B ∘ to A≲B) x
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎
      }
    }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to = to A≲B
    ; from = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          (to A≲B ∘ from A≲B) y
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          (to A≲B ∘ to B≲A) y
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          (from B≲A ∘ to B≲A) y
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎
      }
    }

module ≲-Reasoning where
  infix 1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix 3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl
open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }

-- Equivalence

infix 1 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

⇔-refl : {A : Set} → A ⇔ A
⇔-refl = record { to = λ x → x ; from = λ x → x }

⇔-sym : {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record { to = from A⇔B ; from = to A⇔B }

⇔-trans : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C = record { to = to B⇔C ∘ to A⇔B ; from = from A⇔B ∘ from B⇔C }

-- Bin-embedding

open import part1._Bin using (Bin; ⟨⟩; _I; _O) renaming (inc to incᵇ; from to fromᵇ; to to toᵇ)
open import part1.Induction using (from-to-identity)

ℕ-≲-Bin : ℕ ≲ Bin
ℕ-≲-Bin =
  record
    { to = toᵇ
    ; from = fromᵇ
    ; from∘to = from-to-identity
    }

-- Let's push it

open import part1.Relations using (Can; One; _+ᵇ_; to-can; can-to-from-identity; one-inc-one; to-distrib-+-+ᵇ; +ᵇ-O)
open Can
open One

data CanBin : Set where
  canb : ∀ (b : Bin) → Can b → CanBin

+ᵇ-comm : ∀ (b c : Bin) → b +ᵇ c ≡ c +ᵇ b
+ᵇ-comm ⟨⟩ ⟨⟩ = refl
+ᵇ-comm ⟨⟩ (c O) = refl
+ᵇ-comm ⟨⟩ (c I) = refl
+ᵇ-comm (b O) ⟨⟩ = refl
+ᵇ-comm (b I) ⟨⟩ = refl
+ᵇ-comm (b O) (c O) = cong _O (+ᵇ-comm b c)
+ᵇ-comm (b O) (c I) = cong _I (+ᵇ-comm b c)
+ᵇ-comm (b I) (c O) = cong _I (+ᵇ-comm b c)
+ᵇ-comm (b I) (c I) = cong _O (cong incᵇ (+ᵇ-comm b c))

+ᵇ-one : ∀ {b c : Bin} → One b → One c → One (b +ᵇ c)
+ᵇ-one       one        one                             = one-O one
+ᵇ-one       one        (one-O h2)                      = one-I h2
+ᵇ-one       one        (one-I h2)                      = one-O (one-inc-one h2)
+ᵇ-one {b O} (one-O h1) one        rewrite +ᵇ-comm b ⟨⟩ = one-I h1
+ᵇ-one {b I} (one-I h1) one        rewrite +ᵇ-comm b ⟨⟩ = one-O (one-inc-one h1)
+ᵇ-one       (one-O h1) (one-O h2)                      = one-O (+ᵇ-one h1 h2)
+ᵇ-one       (one-O h1) (one-I h2)                      = one-I (+ᵇ-one h1 h2)
+ᵇ-one       (one-I h1) (one-O h2)                      = one-I (+ᵇ-one h1 h2)
+ᵇ-one       (one-I h1) (one-I h2)                      = one-O (one-inc-one (+ᵇ-one h1 h2))

+ᵇ-can : ∀ {b c : Bin} → Can b → Can c → Can (b +ᵇ c)
+ᵇ-can        (l-one o1)  (l-one o2)                              = l-one (+ᵇ-one o1 o2)
+ᵇ-can        zero        zero                                    = zero
+ᵇ-can        zero        (l-one one)                             = l-one one
+ᵇ-can        zero        (l-one (one-O h2))                      = l-one (one-O h2)
+ᵇ-can        zero        (l-one (one-I h2))                      = l-one (one-I h2)
+ᵇ-can {b O}  (l-one o1)  zero               rewrite +ᵇ-comm b ⟨⟩ = l-one o1
+ᵇ-can {b I}  (l-one o1)  zero               rewrite +ᵇ-comm b ⟨⟩ = l-one o1

_+ᶜ_ : CanBin → CanBin → CanBin
canb k ck +ᶜ canb d cd = canb _ (+ᵇ-can ck cd)
infixl 6 _+ᶜ_

toᶜ : ℕ → CanBin
toᶜ n = canb _ (to-can n)

fromᵇᶜ : Bin → CanBin
fromᵇᶜ = toᶜ ∘ fromᵇ

fromᶜ : CanBin → ℕ
fromᶜ (canb b _) = fromᵇ b

toᵇᶜ : CanBin → Bin
toᵇᶜ (canb b _) = b

≡-one : ∀ {b : Bin} {h1 h2 : One b} → h1 ≡ h2
≡-one {⟨⟩ I} {one} {one} = refl
≡-one {_} {one-O h1} {one-O h2} = cong one-O ≡-one
≡-one {_} {one-I h1} {one-I h2} = cong one-I ≡-one

≡-can : ∀ {b : Bin} {h1 h2 : Can b} → h1 ≡ h2
≡-can {b} {l-one h1} {l-one h2} = cong l-one ≡-one
≡-can {⟨⟩ O} {zero} {zero} = refl
≡-can {⟨⟩ O} {zero} {l-one (one-O ())}
≡-can {⟨⟩ O} {l-one (one-O ())} {zero}

simpl : ∀ {b c : Bin} → ∀ {cb : Can b} {cc : Can c} → b ≡ c → canb b cb ≡ canb c cc
simpl refl = cong (canb _) ≡-can

-- CanBin embeds in Bin

open import Data.Nat.Properties using (+-identityʳ)

to-double-from : ∀ (b : Bin) → One b → toᵇ (fromᵇ b + fromᵇ b) ≡ b O
to-double-from b h
  rewrite to-distrib-+-+ᵇ (fromᵇ b) (fromᵇ b)
        | can-to-from-identity b (l-one h)
  = +ᵇ-O h

inc-to-double-from : ∀ (b : Bin) → One b → incᵇ (toᵇ (fromᵇ b + fromᵇ b)) ≡ b I
inc-to-double-from b h rewrite to-double-from b h = refl

fromᵇᶜ-toᵇᶜ-identity : ∀ (c : CanBin) → (fromᵇᶜ ∘ toᵇᶜ) c ≡ c
fromᵇᶜ-toᵇᶜ-identity (canb (b O) (l-one (one-O ob))) rewrite +-identityʳ (fromᵇ b) = simpl (to-double-from b ob)
fromᵇᶜ-toᵇᶜ-identity (canb (b I) (l-one (one-I ob))) rewrite +-identityʳ (fromᵇ b) = simpl (inc-to-double-from b ob)
fromᵇᶜ-toᵇᶜ-identity (canb (⟨⟩ O) zero) = refl
fromᵇᶜ-toᵇᶜ-identity (canb (⟨⟩ I) (l-one one)) = refl

CanBin-≲-Bin : CanBin ≲ Bin
CanBin-≲-Bin = record { to = toᵇᶜ ; from = fromᵇᶜ ; from∘to = fromᵇᶜ-toᵇᶜ-identity }

-- ℕ is isomorphic to CanBin

canbin-to-from-identity : ∀ (c : CanBin) → (toᶜ ∘ fromᶜ) c ≡ c
canbin-to-from-identity (canb b h) = fromᵇᶜ-toᵇᶜ-identity (canb b h)

ℕ-≃-CanBin : ℕ ≃ CanBin
ℕ-≃-CanBin = record { to = toᶜ ; from = fromᶜ ; from∘to = from-to-identity ; to∘from = canbin-to-from-identity }

import Function using (_∘_)
