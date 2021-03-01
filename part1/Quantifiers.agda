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

-- Existentials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to = ∃-elim
    ; from = λ ∃b→c a ba → ∃b→c ⟨ a , ba ⟩
    ; from∘to = λ _ → refl
    ; to∘from = λ _ → ∀-extensionality λ{⟨ _ , _ ⟩ → refl}
    }

-- Exercises

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{⟨ a , inj₁ Ba ⟩ → inj₁ ⟨ a , Ba ⟩ ; ⟨ a , inj₂ Ca ⟩ → inj₂ ⟨ a , Ca ⟩}
    ; from = λ{(inj₁ ⟨ a , Ba ⟩) → ⟨ a , inj₁ Ba ⟩ ; (inj₂ ⟨ a , Ca ⟩) → ⟨ a , inj₂ Ca ⟩}
    ; from∘to = λ{⟨ a , inj₁ x ⟩ → refl ; ⟨ a , inj₂ y ⟩ → refl}
    ; to∘from = λ{(inj₁ ⟨ a , Ba ⟩) → refl ; (inj₂ ⟨ a , Ca ⟩) → refl}
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ Ba , Ca ⟩ ⟩ = ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩

-- ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} → (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
-- doesn't hold because different existentials are of different types

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to = λ{⟨ aa , Btri ⟩ → inj₁ Btri ; ⟨ bb , Btri ⟩ → inj₂ (inj₁ Btri) ; ⟨ cc , Btri ⟩ → inj₂ (inj₂ Btri)}
    ; from = λ{(inj₁ Baa) → ⟨ aa , Baa ⟩ ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩ ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩}
    ; from∘to = λ{⟨ aa , Btri ⟩ → refl ; ⟨ bb , Btri ⟩ → refl ; ⟨ cc , Btri ⟩ → refl}
    ; to∘from = λ{(inj₁ Baa) → refl ; (inj₂ (inj₁ Bbb)) → refl ; (inj₂ (inj₂ Bcc)) → refl}
    }
