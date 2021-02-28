module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import part1.Isomorphism using (_≃_; extensionality)
open import Level using (Level)

-- Negation

¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
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

open import part1.Connectives using (→-distrib-⊎; _×_; proj₁; proj₂; _⊎_; inj₁; inj₂) renaming (⟨_,_⟩ to _,_)

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

-- Classical laws: signatures

em-Type        = ∀ {A : Set}   → A ⊎ ¬ A
¬¬-elim-Type   = ∀ {A : Set}   → ¬ ¬ A → A
peirce-Type    = ∀ {A B : Set} → ((A → B) → A) → A
→-⊎-Type       = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
de-morgan-Type = ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

-- Classical laws: implications
--   at this point we haven't yet postulated the law of excluded middle

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

em-implies-all : em-Type → (¬¬-elim-Type × peirce-Type × →-⊎-Type × de-morgan-Type)
em-implies-all em =
  (λ {A} ¬¬a → case em {A} of
    λ{(inj₁ a)  → a
    ; (inj₂ ¬a) → (⊥-elim ∘ ¬¬a) ¬a}) , (
  (λ {A} f → case em {A} of
    λ{(inj₁ a)  → a
    ; (inj₂ ¬a) → f (⊥-elim ∘ ¬a)}) , (
  (λ {A} a→b → case em {A} of
    λ{(inj₁ a)  → inj₂ (a→b a)
    ; (inj₂ ¬a) → inj₁ ¬a} ),
  (λ {A} {B} ¬× → case em {B} of case em {A} of
    λ{(inj₂ ¬a) (inj₂ ¬b) → ⊥-elim (¬× (¬a , ¬b))
    ; (inj₂ ¬a) (inj₁ b)  → inj₂ b
    ; (inj₁ a)  _         → inj₁ a} )))

¬¬-elim-implies-all : ¬¬-elim-Type → (em-Type × peirce-Type × →-⊎-Type × de-morgan-Type)
¬¬-elim-implies-all ¬¬-elim =
  ¬¬-elim (λ z → z (inj₂ (z ∘ inj₁))) , (
  (λ h   → ¬¬-elim λ ¬a   → contraposition h ¬a (⊥-elim ∘ ¬a)) , (
  (λ a→b → ¬¬-elim λ f    → f (inj₁ (f ∘ inj₂ ∘ a→b))) ,
  λ ¬×   → ¬¬-elim λ ¬a⊎b → ¬× ((¬a⊎b ∘ inj₁) , ¬a⊎b ∘ inj₂)
  ))

peirce-implies-all : peirce-Type → (em-Type × ¬¬-elim-Type × →-⊎-Type × de-morgan-Type)
peirce-implies-all h =
  em′ h , (
  proj₁ cheat , (
  (λ a→b → h (λ f → inj₁ (f ∘ inj₂ ∘ a→b))) ,
  (proj₂ ∘ proj₂ ∘ proj₂) cheat
  ))
  where
    em′ : peirce-Type → em-Type
    em′ h = h (λ z → inj₂ (z ∘ inj₁))
    cheat = (em-implies-all ∘ em′) h

--   I'm tired of this. ¯\_(ツ)_/¯ Moving on.

-- Classical laws: excluded middle

postulate
  em : em-Type

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = (k ∘ inj₂) (k ∘ inj₁)

-- Classical laws: proofs

¬¬-elim : ¬¬-elim-Type
¬¬-elim   = (proj₁ ∘ em-implies-all) em

peirce : peirce-Type
peirce    = (proj₁ ∘ proj₂ ∘ em-implies-all) em

→-⊎ : →-⊎-Type
→-⊎       = (proj₁ ∘ proj₂ ∘ proj₂ ∘ em-implies-all) em

de-morgan : de-morgan-Type
de-morgan = (proj₂ ∘ proj₂ ∘ proj₂ ∘ em-implies-all) em

-- Stable

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} {sa : Stable A} {sb : Stable B} → Stable (A × B)
×-stable = ¬¬-elim
