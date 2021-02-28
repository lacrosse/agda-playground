module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import part1.Isomorphism using (_≃_; extensionality)

-- Negation

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim na a = na a

infix 3 ¬_

-- Classical:      A ⇔ ¬ ¬ A
-- Intuitionistic: A → ¬ ¬ A

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a neg = neg a

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim h a = h λ neg → neg a

open import Function using (_∘_)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition h notb = notb ∘ h

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x _ = extensionality λ x → ⊥-elim (¬x x)

-- Exercises

open import part1.Relations using (_<_; _>_)
open _<_

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s h) = <-irreflexive h
