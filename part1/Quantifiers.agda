module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
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

-- An existential example
open import part1.Relations using (even; odd; zero; suc)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (     m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd  n → ∃[ m ] ( 1 + m * 2 ≡ n)

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc on) with odd-∃ on
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (suc en) with even-∃ en
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd  n

∃-even ⟨ zero , refl ⟩ = zero
∃-even ⟨ suc om , refl ⟩ = suc (∃-odd ⟨ om , refl ⟩)

∃-odd ⟨ om , refl ⟩ = suc (∃-even ⟨ om , refl ⟩)

-- Exercise ∃-even-odd

open import part1.Induction using (+-identityʳ; +-suc; +-comm; +-assoc)

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd  n

∃-even′ ⟨ zero , refl ⟩ = zero
∃-even′ ⟨ suc om , refl ⟩ = suc (∃-odd′ ⟨ om , helper om ⟩)
  where
    helper : ∀ (n : ℕ) → n + (n + zero) + 1 ≡ n + suc (n + zero)
    helper n
      rewrite +-comm n 0
            | +-comm (n + n) 1
            | +-suc n n
      = refl

∃-odd′ ⟨ om , refl ⟩
  rewrite +-identityʳ om | +-comm (om + om) 1
  = suc (n+n-even om)
  where
    n+n-even : ∀ (n : ℕ) → even(n + n)
    n+n-even zero = zero
    n+n-even (suc n) rewrite +-suc n n = suc (suc (n+n-even n))

-- Exercise ∃-|-≤
open import Data.Nat using (_≤_)
open import Agda.Builtin.Nat using (_-_)
open _≤_

-+suc≡suc : ∀ (m n : ℕ) → n ≤ m → m - n + suc n ≡ suc m
-+suc≡suc m 0 z≤n rewrite +-comm m 1 = refl
-+suc≡suc (suc m) (suc n) (s≤s n≤m)
  rewrite +-suc (m - n) (suc n)
  rewrite -+suc≡suc m n n≤m
  = refl

≤-implies-∃ : ∀ {y z : ℕ} → y ≤ z → (∃[ x ] (x + y ≡ z))
≤-implies-∃ {_} {z} z≤n = ⟨ z , +-identityʳ z ⟩
≤-implies-∃ {suc y} {suc z} (s≤s y≤z) = ⟨ z - y , -+suc≡suc z y y≤z ⟩

≡-implies-≤ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
≡-implies-≤ {suc m} refl = s≤s (≡-implies-≤ refl)
≡-implies-≤ {zero} refl = z≤n

≤-+ : ∀ {m n : ℕ} → m ≤ n + m
≤-+ {zero} {n} = z≤n
≤-+ {suc m} {zero} = s≤s ≤-+
≤-+ {suc m} {suc n} rewrite sym (+-assoc n 1 m) = s≤s ≤-+

∃-implies-≤ : ∀ {y z : ℕ} → (∃[ x ] (x + y ≡ z)) → y ≤ z
∃-implies-≤ ⟨ zero , refl ⟩ = ≡-implies-≤ refl
∃-implies-≤ {zero} ⟨ suc x , refl ⟩ = z≤n
∃-implies-≤ {suc y} ⟨ suc x , refl ⟩ rewrite sym (+-assoc x 1 y) = s≤s ≤-+
