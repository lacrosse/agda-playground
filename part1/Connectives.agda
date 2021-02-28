module part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

-- Conjunction

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ a , b ⟩ = a

proj₂ : ∀ {A B : Set} → A × B → B
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
