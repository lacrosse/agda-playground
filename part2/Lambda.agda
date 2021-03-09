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

-- Exercise mul

mul : Term
mul =
  μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
    ]

mulᶜ : Term
mulᶜ =
  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · (ƛ "acc" ⇒ plusᶜ · ` "n" · ` "acc" · sucᶜ · ` "z") · ` "z"

-- Exercise primed

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ] = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ =
  μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ n
    |suc m ⇒ `suc (+ · m · n)
    ]
  where
    + = ` "+"
    m = ` "m"
    n = ` "n"

mul′ : Term
mul′ =
  μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ z
    |suc m ⇒ plus · n · (* · m · n)
    ]
  where
    * = ` "*"
    m = ` "m"
    n = ` "n"
    z = `zero

-- Values

data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc : ∀ {V} → Value V → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term

(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x

(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]

(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

`zero [ y := V ] = `zero

(`suc M) [ y := V ] = `suc (M [ y := V ])

(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]

(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

-- Quiz
-- Answer: 3

-- Exercise _[_:=_]′

infix 9 _[_:=_]′

_[_:=_]′ : Term → Id → Term → Term

subst-preserve : (Id → Term → Term) → Id → Term → Id → Term → Term
subst-preserve f x term y V with x ≟ y
... | yes _ = f x term
... | no  _ = f x (term [ y := V ]′)

(` x) [ y := V ]′ with x ≟ y
... | yes _ = V
... | no  _ = ` x

(L · M) [ y := V ]′ = L [ y := V ]′ · M [ y := V ]′

`zero [ y := V ]′ = `zero

(`suc M) [ y := V ]′ = `suc (M [ y := V ]′)

_[_:=_]′ (ƛ x ⇒ N) = subst-preserve ƛ_⇒_ x N
_[_:=_]′ (μ_⇒_ x N) = subst-preserve μ_⇒_ x N
_[_:=_]′ (case L [zero⇒ M |suc x ⇒ N ]) y V
  = subst-preserve (case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc_⇒_]) x N y V

-- Reduction

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M} → L —→ L′ → L · M —→ L′ · M
  ξ-·₂ : ∀ {V M M′} → Value V → M —→ M′ → V · M —→ V · M′
  β-ƛ : ∀ {x N V} → Value V → (ƛ x ⇒ N) · V —→ N [ x := V ]
  ξ-suc : ∀ {M M′} → M —→ M′ → `suc M —→ `suc M′
  ξ-case : ∀ {x L L′ M N} → L —→ L′ → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]
  β-zero : ∀ {x M N} → case `zero [zero⇒ M |suc x ⇒ N ] —→ M
  β-suc : ∀ {x V M N} → Value V → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]
  β-μ : ∀ {x M} → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

-- Quiz
-- Answers: 1, 2, 2

-- Reflexive and transitive closure

infix 2 _—↠_
infix 1 begin_
infixr 2 _—↠⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M → M —↠ M
  _—↠⟨_⟩_ : ∀ L {M N} → L —→ M → M —↠ N → L —↠ N

begin_ : ∀ {M N} → M —↠ N → M —↠ N
begin_ M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where
  step′ : ∀ {M N} → M —→ N → M —↠′ N
  refl′ : ∀ {M} → M —↠′ M
  trans′ : ∀ {L M N} → L —↠′ M → M —↠′ N → L —↠′ N

-- Exercise

open import part1.Isomorphism using (_≲_)

—↠-trans : ∀ {L M N} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (_ ∎) h = h
—↠-trans (_ —↠⟨ f ⟩ g) h = _ —↠⟨ f ⟩ —↠-trans g h

—↠≲—↠′ : ∀ {M N} → M —↠ N ≲ M —↠′ N
—↠≲—↠′ =
  record
    { to = to′
    ; from = from′
    ; from∘to = ft-identity
    }
  where
    to′ : ∀ {M N} → M —↠ N → M —↠′ N
    to′ (_ ∎) = refl′
    to′ (_ —↠⟨ g ⟩ h) = trans′ (step′ g) (to′ h)
    from′ : ∀ {M N} → M —↠′ N → M —↠ N
    from′ (step′ x) = _ —↠⟨ x ⟩ _ ∎
    from′ refl′ = _ ∎
    from′ (trans′ g h) = —↠-trans (from′ g) (from′ h)
    ft-identity : ∀ {A B} (x : A —↠ B) → from′ (to′ x) ≡ x
    ft-identity (_ ∎) = refl
    ft-identity (_ —↠⟨ _ ⟩ A—↠B) rewrite ft-identity A—↠B = refl
