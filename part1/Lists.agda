module part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import part1.Isomorphism using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- OK I can't stop myself now

first-ℕ : ℕ → List ℕ
first-ℕ = aux []
  where
    aux : List ℕ → ℕ → List ℕ
    aux acc zero    = acc
    aux acc (suc n) = aux (n ∷ acc) n

first-5 : List ℕ
first-5 = first-ℕ 5

_ : first-5 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
_ = refl

rev : ∀ {A : Set} → List A → List A
rev {A} = aux []
  where
    aux : List A → List A → List A
    aux acc []      = acc
    aux acc (h ∷ t) = aux (h ∷ acc) t

rev-first-5 : List ℕ
rev-first-5 = rev first-5

_ : rev-first-5 ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
_ = refl

map : ∀ {A B : Set} → (A → B) → List A → List B
map {A} {B} f []      = []
map {A} {B} f (h ∷ t) = f h ∷ map f t

rev+1 : List ℕ
rev+1 = map (_+_ 1) rev-first-5

_ : rev+1 ≡ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

open Function using (_|>_)

first-4-pairs : List (List ℕ)
first-4-pairs =
  first-ℕ 4
  |> map (λ x →
    2
    |> first-ℕ
    |> map (_+_ x)
  )
  |> rev
  |> map rev

_ : first-4-pairs ≡
  (4 ∷ 3 ∷ []) ∷
  (3 ∷ 2 ∷ []) ∷
  (2 ∷ 1 ∷ []) ∷
  (1 ∷ 0 ∷ []) ∷
  []
_ = refl

-- End rant, resume PFLA

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
