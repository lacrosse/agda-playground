module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import part1.Isomorphism using (_≃_; extensionality)

-- Universals

∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A) → B M
∀-elim = λ L → L

open import Function using (_∘_)

-- Exercises

∀-distrib-× : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ →× → ⟨ proj₁ ∘ →× , proj₂ ∘ →× ⟩
    ; from = λ →×→ a → ⟨ proj₁ →×→ a , proj₂ →×→ a ⟩
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ →b) a = inj₁ (→b a)
⊎∀-implies-∀⊎ (inj₂ →c) a = inj₂ (→c a)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
    { to = λ z → ⟨ z aa , ⟨ z bb , z cc ⟩ ⟩
    ; from = λ{⟨ fst , _ ⟩ aa → fst ; ⟨ _ , ⟨ snd , _ ⟩ ⟩ bb → snd ; ⟨ _ , ⟨ _ , trd ⟩ ⟩ cc → trd}
    ; from∘to = λ{f → ∀-extensionality λ{aa → refl ; bb → refl ; cc → refl}}
    ; to∘from = λ{⟨ fst , ⟨ snd , trd ⟩ ⟩ → refl}
    }
