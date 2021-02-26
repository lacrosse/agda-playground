module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {X Y Z : Set} {x₁ x₂ : X} {y₁ y₂ : Y} (f : X → Y → Z)
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl h = refl

subst : ∀ {A : Set} {x y : A} (f : A → Set) → x ≡ y → f x → f y
subst _ refl h = h
