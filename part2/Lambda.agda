module part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
-- ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
-- ·  U+00B7  MIDDLE DOT (\cdot)
-- —  U+2014  EM DASH (\em)
-- ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
-- ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
-- β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
-- Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
-- ≠  U+2260  NOT EQUAL TO (\=n or \ne)
-- ∋  U+220B  CONTAINS AS MEMBER (\ni)
-- ∅  U+2205  EMPTY SET (\0)
-- ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
-- ⦂  U+2982  Z NOTATION TYPE COLON (\:)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_ : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_ : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_ : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus =
  μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ]

twoᶜ :  Term
twoᶜ =
  ƛ "s" ⇒ ƛ "z" ⇒
  ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =
  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ =
  ƛ "n" ⇒
  `suc (` "n")
