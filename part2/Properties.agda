module part2.Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
  open import Data.String using (String; _≟_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Function using (_∘_)
  open import part1.Isomorphism
  open import part2.Lambda
