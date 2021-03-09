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

one : Term
one = `suc `zero

two : Term
two = `suc one

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
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′
  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]
  ξ-suc : ∀ {M M′}
    → M —→ M′
    → `suc M —→ `suc M′
  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]
  β-zero : ∀ {x M N}
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M
  β-suc : ∀ {x V M N}
    → Value V
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]
  β-μ : ∀ {x M}
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

-- Quiz
-- Answers: 1, 2, 2

-- Reflexive and transitive closure

infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M → M —↠ M
  _—→⟨_⟩_ : ∀ L {M N} → L —→ M → M —↠ N → L —↠ N

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
—↠-trans (_ —→⟨ f ⟩ g) h = _ —→⟨ f ⟩ —↠-trans g h

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
    to′ (_ —→⟨ g ⟩ h) = trans′ (step′ g) (to′ h)
    from′ : ∀ {M N} → M —↠′ N → M —↠ N
    from′ (step′ x) = _ —→⟨ x ⟩ _ ∎
    from′ refl′ = _ ∎
    from′ (trans′ g h) = —↠-trans (from′ g) (from′ h)
    ft-identity : ∀ {A B} (x : A —↠ B) → from′ (to′ x) ≡ x
    ft-identity (_ ∎) = refl
    ft-identity (_ —→⟨ _ ⟩ A—↠B) rewrite ft-identity A—↠B = refl

postulate
  confluence : ∀ {L M N} → ((L —↠ M) × (L —↠ N)) → ∃[ P ] ((M —↠ P) × (N —↠ P))
  diamond : ∀ {L M N} → ((L —→ M) × (L —→ N)) → ∃[ P ] ((M —↠ P) × (N —↠ P))
  deterministic : ∀ {L M N} → L —→ M → L —→ N → M ≡ N

-- Examples

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two)]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒ case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

-- Exercise

_ : plus · one · one —↠ two
_ =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · `zero · one
    )
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc (
      (ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · one
    )
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (
      case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
    )
  —→⟨ ξ-suc β-zero ⟩
    two
  ∎

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Quiz
-- Answers: 2, 6

infixl 5 _,_⦂_

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

-- Exercise Context-≃

open part1.Isomorphism using (_≃_)
open Data.Product using (_,_)

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to = to
    ; from = from
    ; from∘to = ft-identity
    ; to∘from = tf-identity
    }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (c , id ⦂ type) = (id , type) ∷ (to c)
    from : List (Id × Type) → Context
    from [] = ∅
    from ((id , type) ∷ xs) = (from xs) , id ⦂ type
    ft-identity : ∀ (c : Context) → from (to c) ≡ c
    ft-identity ∅ = refl
    ft-identity (c , id ⦂ type) rewrite ft-identity c = refl
    tf-identity : ∀ (xs : List (Id × Type)) → to (from xs) ≡ xs
    tf-identity [] = refl
    tf-identity ((id , type) ∷ xs) rewrite tf-identity xs = refl

-- Lookup

infix 4 _∋_⦂_
data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A → Γ , y ⦂ B ∋ x ⦂ A

S′ : ∀ {Γ x y A B} → {x≢y : False (x ≟ y)} → Γ ∋ x ⦂ A → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- Typing

infix 4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ⦂ A
  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
    → Γ ⊢ L · M ⦂ B
  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
    → Γ ⊢ `zero ⦂ `ℕ
  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
    → Γ ⊢ `suc M ⦂ `ℕ
  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A
  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
    → Γ ⊢ μ x ⇒ M ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` (S′ Z) · (⊢` (S′ Z) · ⊢` Z)))

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z)) (⊢` Z) (⊢suc (⊢` (S′ (S′ (S′ Z))) · ⊢` Z · ⊢` (S′ Z))))))

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S x≢x _) = ⊥-elim (x≢x refl)
∋-injective (S x≢x _) Z = ⊥-elim (x≢x refl)
∋-injective (S _ g) (S _ h) = ∋-injective g h

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

-- Quiz
-- *
--  1. `ℕ
--  2. impossible: requires "x" to be typed as (`ℕ ⇒ `ℕ) ⇒ B
--  3. `ℕ ⇒ `ℕ (same as y)
-- *
--  1. impossible: requires A ≡ A ⇒ B
--  2. B ≡ D ⇒ E; A ≡ E ⇒ F; C ≡ D ⇒ F

-- Exercise ⊢mul

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul =
  ⊢μ (
    ⊢ƛ (
      ⊢ƛ (
        ⊢case
          (⊢` (S′ Z))
          ⊢zero
          (
            ⊢μ (
              ⊢ƛ (
                ⊢ƛ (
                  ⊢case
                    (⊢` (S′ Z))
                    (⊢` Z)
                    (
                      ⊢suc
                        (
                          ⊢` (S′ (S′ (S′ Z)))
                          ·
                          ⊢` Z
                          ·
                          ⊢` (S′ Z)
                        )
                    )
                )
              )
            )
            ·
            ⊢` (S′ Z)
            ·
            (
              ⊢` (S′ (S′ (S′ Z)))
              ·
              ⊢` Z
              ·
              ⊢` (S′ Z)
            )
          )
      )
    )
  )
