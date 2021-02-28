module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
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

open import part1.Connectives using (→-distrib-⊎; _×_; _⊎_; inj₁; inj₂) renaming (⟨_,_⟩ to _,_)

data <-Trichotomy (m n : ℕ) : Set where
  fw : ¬ (m < n) × ¬ (m ≡ n) × m > n → <-Trichotomy m n
  eq : ¬ (m < n) × m ≡ n × ¬ (m > n) → <-Trichotomy m n
  bw : m < n × ¬ (m ≡ n) × ¬ (m > n) → <-Trichotomy m n

≡-suc : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
≡-suc refl = refl

trichotomy : ∀ (m n : ℕ) → <-Trichotomy m n
trichotomy zero zero = eq ( (λ()) , (refl) , (λ()))
trichotomy zero (suc n) = bw (0<s , (λ()) , (λ()))
trichotomy (suc m) zero = fw ((λ()) , (λ()) , 0<s)
trichotomy (suc m) (suc n) = h (trichotomy m n)
  where
    h : <-Trichotomy m n → <-Trichotomy (suc m) (suc n)
    h (fw (a , b , c)) = fw ((λ{(s<s h) → a h}) , b ∘ ≡-suc , s<s c)
    h (eq (a , b , c)) = eq ((λ{(s<s h) → a h}) , cong suc b , λ{(s<s h) → c h})
    h (bw (a , b , c)) = bw (s<s a , b ∘ ≡-suc , λ{(s<s h) → c h})

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

-- Excluded middle

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = (k ∘ inj₂) (k ∘ inj₁)

excluded-middle : ∀ {A : Set} → A ⊎ ¬ A
excluded-middle = {!   !}

¬¬-elim : ∀ {A : Set} → ¬ ¬ A → A
¬¬-elim h = {!   !}

peirce : ∀ {A B : Set} → ((A → B) → A) → A
peirce = {!   !}

→-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
→-⊎ = {!   !}

de-morgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
de-morgan = {!   !}

-- Stable

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} {sa : Stable A} {sb : Stable B} → Stable (A × B)
×-stable = ¬¬-elim
