module part2.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import part1.Isomorphism
open import part2.Lambda

-- Values do not reduce

V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ (V-suc vm) (ξ-suc M—→N) = V¬—→ vm M—→N

flip : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
flip f b a = f a b

—→¬V : ∀ {M N} → M —→ N → ¬ Value M
—→¬V = flip V¬—→

-- Canonical forms

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-λ : ∀ {x A N B} → ∅ , x ⦂ A ⊢ N ⦂ B → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  C-zero : Canonical `zero ⦂ `ℕ
  C-suc : ∀ {V} → Canonical V ⦂ `ℕ → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical (⊢ƛ typing) V-ƛ = C-λ typing
canonical ⊢zero V-zero = C-zero
canonical (⊢suc typing) (V-suc vv) = C-suc (canonical typing vv)

value : ∀ {M A} → Canonical M ⦂ A → Value M
value (C-λ typing) = V-ƛ
value C-zero = V-zero
value (C-suc can) = V-suc (value can)

typed : ∀ {M A} → Canonical M ⦂ A → ∅ ⊢ M ⦂ A
typed (C-λ typing) = ⊢ƛ typing
typed C-zero = ⊢zero
typed (C-suc can) = ⊢suc (typed can)

data Progress (M : Term) : Set where
  step : ∀ {N} → M —→ N → Progress M
  done : Value M → Progress M

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
progress (⊢ƛ _) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L | progress ⊢M
... | step L—→N | _ = step (ξ-·₁ L—→N)
... | done vl | step M—→N = step (ξ-·₂ vl M—→N)
... | done vl | done vm with canonical ⊢L vl
... | C-λ typing = step (β-ƛ vm)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M—→N = step (ξ-suc M—→N)
... | done vm = done (V-suc vm)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→ = step (ξ-case L—→)
... | done vl with canonical ⊢L vl
... | C-zero = step β-zero
... | C-suc can = step (β-suc (value can))
progress (⊢μ _) = step β-μ

-- Exercises

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ =
  record
    { to = λ{(step M—→) → inj₂ (_ , M—→) ; (done v) → inj₁ v}
    ; from = λ{(inj₁ v) → done v ; (inj₂ (_ , M—→)) → step M—→}
    ; from∘to = λ{(step _) → refl ; (done _) → refl}
    ; to∘from = λ{(inj₁ _) → refl ; (inj₂ _) → refl}
    }

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ M ⊢M with progress {M} ⊢M
... | step M—→ = inj₂ (_ , M—→)
... | done vm = inj₁ vm

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | step M—→ = no (—→¬V M—→)
... | done vm = yes vm
