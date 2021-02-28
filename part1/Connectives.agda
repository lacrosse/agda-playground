module part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import part1.Isomorphism using (_≃_; _≲_; extensionality)
open part1.Isomorphism.≃-Reasoning
open import Level

-- Conjunction

data _×_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  ⟨_,_⟩ : A → B → A × B

infixr 2 ⟨_,_⟩

proj₁ : ∀ {ℓ : Level} {A B : Set ℓ} → A × B → A
proj₁ ⟨ a , b ⟩ = a

proj₂ : ∀ {ℓ : Level} {A B : Set ℓ} → A × B → B
proj₂ ⟨ a , b ⟩ = b

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ a , b ⟩ = refl

infixr 2 _×_

-- Conjunction as type

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true , aa ⟩ = 1
×-count ⟨ true , bb ⟩ = 2
×-count ⟨ true , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ{⟨ a , b ⟩ → ⟨ b , a ⟩}
    ; from = λ{⟨ a , b ⟩ → ⟨ b , a ⟩}
    ; from∘to = λ{⟨ a , b ⟩ → refl}
    ; to∘from = λ{⟨ a , b ⟩ → refl}
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩}
    ; from = λ{⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩}
    ; from∘to = λ{⟨ ⟨ a , b ⟩ , c ⟩ → refl}
    ; to∘from = λ{⟨ a , ⟨ b , c ⟩ ⟩ → refl}
    }

-- Exercise

open import part1.Isomorphism using (_⇔_)
open _⇔_

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ a⇔b → ⟨ to a⇔b , from a⇔b ⟩
    ; from = λ{⟨ a→b , b→a ⟩ → record { to = a→b ; from = b→a }}
    ; from∘to = λ a⇔b → refl
    ; to∘from = λ{⟨ a→b , b→a ⟩ → refl}
    }

-- Truth

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- Truth as empty record

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ{⟨ _ , a ⟩ → a}
    ; from = λ a → ⟨ tt , a ⟩
    ; from∘to = λ{⟨ tt , _ ⟩ → refl}
    ; to∘from = λ a → refl
    }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- Disjunction

data _⊎_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ a→c _   (inj₁ a) = a→c a
case-⊎ _   b→c (inj₂ b) = b→c b

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ a) = refl
η-⊎ (inj₂ b) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ a) = refl
uniq-⊎ h (inj₂ b) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true) = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa) = 3
⊎-count (inj₂ bb) = 4
⊎-count (inj₂ cc) = 5

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{(inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b}
    ; from = λ{(inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a}
    ; from∘to = λ{(inj₁ x) → refl ; (inj₂ x) → refl}
    ; to∘from = λ{(inj₁ x) → refl ; (inj₂ x) → refl}
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{(inj₁ (inj₁ a)) → inj₁ a ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b) ; (inj₂ c) → inj₂ (inj₂ c)}
    ; from = λ{(inj₁ a) → inj₁ (inj₁ a) ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b) ; (inj₂ (inj₂ c)) → inj₂ c}
    ; from∘to = λ{(inj₁ (inj₁ a)) → refl ; (inj₁ (inj₂ b)) → refl ; (inj₂ c) → refl}
    ; to∘from = λ{(inj₁ a) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ c)) → refl}
    }

-- False

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ _ ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{(inj₂ a) → a}
    ; from = λ a → inj₂ a
    ; from∘to = λ{(inj₂ _) → refl}
    ; to∘from = λ _ → refl
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

-- Implication

-- Modus ponens

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim a→b a = a→b a

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
... | aa | aa = 1
... | aa | bb = 2
... | aa | cc = 3
... | bb | aa = 4
... | bb | bb = 5
... | bb | cc = 6
... | cc | aa = 7
... | cc | bb = 8
... | cc | cc = 9

schönfinkelisation : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
schönfinkelisation =
  record
    { to = λ{f ⟨ a , b ⟩ → f a b}
    ; from = λ{g a b → g ⟨ a , b ⟩}
    ; from∘to = λ{f → refl}
    ; to∘from = λ{g → extensionality λ{⟨ a , b ⟩ → refl}}
    }

currying = schönfinkelisation

-- Distributions

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ{⟨ f , _ ⟩ (inj₁ a) → f a ; ⟨ _ , g ⟩ (inj₂ b) → g b}
    ; from∘to = λ{f → extensionality λ{(inj₁ a) → refl ; (inj₂ b) → refl}}
    ; to∘from = λ{⟨ f , g ⟩ → refl}
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distrib-× =
  record
    { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from = λ{⟨ g , h ⟩ a → ⟨ g a , h a ⟩}
    ; from∘to = λ f → extensionality (η-× ∘ f)
    ; to∘from = λ{⟨ g , h ⟩ → refl}
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ {⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩ ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩}
    ; from = λ{(inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩ ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩}
    ; from∘to = λ{⟨ inj₁ a , c ⟩ → refl ; ⟨ inj₂ b , c ⟩ → refl}
    ; to∘from = λ{(inj₁ ⟨ a , c ⟩) → refl ; (inj₂ ⟨ b , c ⟩) → refl}
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ {(inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩ ; (inj₂ c) → ⟨ inj₂ c , inj₂ c ⟩}
    ; from = λ
      { ⟨ inj₁ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
      ; ⟨ inj₂ c , inj₁ _ ⟩ → inj₂ c
      ; ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c
      ; ⟨ inj₂ c , inj₂ _ ⟩ → inj₂ c
      }
    ; from∘to = λ{(inj₁ ⟨ a , b ⟩) → refl ; (inj₂ c) → refl}
    }

-- Weak distributive law

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
