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

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[]        ++ b = b
(ah ∷ at) ++ b = ah ∷ (at ++ b)

_ : [ 0 , 1 , 2 ] ++ [ 93 , 42 ] ≡ [ 0 , 1 , 2 , 93 , 42 ]
_ = refl

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

rev-aux : ∀ {A : Set} → List A → List A → List A
rev-aux acc []      = acc
rev-aux acc (h ∷ t) = rev-aux (h ∷ acc) t

rev : ∀ {A : Set} → List A → List A
rev {A} = rev-aux {A} []

-- Just wow.

rev-first-5 : List ℕ
rev-first-5 = rev first-5

_ : rev-first-5 ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
_ = refl

map : ∀ {A B : Set} → (A → B) → List A → List B
map {A} {B} f []      = []
map {A} {B} f (h ∷ t) = f h ∷ map f t

rev+1 : List ℕ
rev+1 = map (_+ 1) rev-first-5

_ : rev+1 ≡ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

open Function using (_|>_)

first-4-pairs : List (List ℕ)
first-4-pairs =
  first-ℕ 4
  |> map (λ x →
    2
    |> first-ℕ
    |> map (_+ x)
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

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- Length

length : ∀ {A : Set} (list : List A) → ℕ
length []         = 0
length (_ ∷ list) = 1 + length list

_ : length first-4-pairs ≡ 4
_ = refl

length-distrib-++-+ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-distrib-++-+ []       ys = refl
length-distrib-++-+ (x ∷ xs) ys = cong suc (length-distrib-++-+ xs ys)

-- Reverse done already.

-- Exercises

rev-aux-++ : ∀ {A : Set} (xs ys : List A) → rev-aux xs ys ≡ rev ys ++ xs
rev-aux-++ [] [] = refl
rev-aux-++ (x ∷ xs) [] = refl
rev-aux-++ xs (y ∷ ys)
  rewrite rev-aux-++ (y ∷ xs) ys
        | rev-aux-++ [ y ] ys
        | ++-assoc (rev-aux [] ys) [ y ] (xs)
  = refl

rev-++-distrib : ∀ {A : Set} (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-++-distrib [] ys = sym (++-identityʳ (rev ys))
rev-++-distrib xs [] = cong rev (++-identityʳ xs)
rev-++-distrib (x ∷ xs) (y ∷ ys)
  rewrite rev-aux-++ [ x ] (xs ++ y ∷ ys)
        | rev-++-distrib xs (y ∷ ys)
        | rev-aux-++ [ x ] xs
        | rev-aux-++ [ y ] ys
        | ++-assoc (rev ys ++ [ y ]) (rev xs) [ x ]
  = refl

rev-involutive : ∀ {A : Set} (xs : List A) → rev (rev xs) ≡ xs
rev-involutive [] = refl
rev-involutive (x ∷ xs)
  rewrite rev-aux-++ [ x ] xs
        | rev-++-distrib xs [ x ]
        | rev-++-distrib (rev xs) [ x ]
        | rev-involutive xs
  = refl

-- Faster reverse
-- Done already.

-- Map
-- Done already.

-- Exercise

open part1.Isomorphism using (extensionality)

map-compose-list : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-list _ _ [] = refl
map-compose-list f g (x ∷ xs) rewrite map-compose-list f g xs = refl

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} → map (g ∘ f) ≡ map g ∘ map f
map-compose = extensionality (map-compose-list _ _)

map-++-distribute : ∀ {A B : Set} (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute _ [] _ = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree a→c _   (leaf a)            = leaf (a→c a)
map-Tree a→c b→d (node left b right) = node (map-Tree a→c b→d left) (b→d b) (map-Tree a→c b→d right)

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _ acc []       = acc
foldr f acc (x ∷ xs) = f x (foldr f acc xs)

sum : List ℕ → ℕ
sum = foldr _+_ 0

-- Exercises

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (f : A → B → B) (e : B) (xs ys : List A) → foldr f e (xs ++ ys) ≡ foldr f (foldr f e ys) xs
foldr-++ _ _ [] ys = refl
foldr-++ f _ (x ∷ xs) ys = cong (f x) (foldr-++ f _ xs ys)

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = cong (x ∷_) (foldr-∷ xs)

++-foldr-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr-∷ [] _ = refl
++-foldr-∷ (x ∷ xs) ys = cong (x ∷_) (++-foldr-∷ xs ys)

map-is-foldr-list : ∀ {A B : Set} (f : A → B) (ys : List A) → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr-list _ [] = refl
map-is-foldr-list f (x ∷ xs) rewrite map-is-foldr-list f xs = cong (f x ∷_) refl

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr = extensionality ∘ map-is-foldr-list

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree fl _ (leaf a) = fl a
fold-Tree fl f (node left b right) = f (fold-Tree fl f left) b (fold-Tree fl f right)

_ : fold-Tree (λ x → x) (λ left center right → left + center + right) (node (node (leaf 0) 93 (leaf 3)) 1 (leaf 931)) ≡ 1028
_ = refl

map-is-fold-Tree-tree : ∀ {A B C D : Set} (fl : A → C) (fn : B → D) (tree : Tree A B) → map-Tree fl fn tree ≡ fold-Tree (λ a → leaf (fl a)) (λ left b right → node left (fn b) right) tree
map-is-fold-Tree-tree _ _ (leaf a) = refl
map-is-fold-Tree-tree fl fn (node left b right)
  rewrite map-is-fold-Tree-tree fl fn left
        | map-is-fold-Tree-tree fl fn right
  = refl

map-is-fold-Tree : ∀ {A B C D : Set} {fl : A → C} {fn : B → D} → map-Tree fl fn ≡ fold-Tree (λ a → leaf (fl a)) (λ left b right → node left (fn b) right)
map-is-fold-Tree = extensionality (map-is-fold-Tree-tree _ _)

-- sum-downFrom

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

open Data.Nat.Properties using (*-comm; +-comm; *-distribʳ-+; *-distribˡ-∸; *-identityʳ; +-∸-assoc; m+n∸m≡n; m≤m+n; m≤m*n; _<?_)
open Data.Nat using (_<_)

n≤n : ∀ {n : ℕ} → n ≤ n
n≤n {zero} = z≤n
n≤n {suc n} = s≤s n≤n

n≤n*n : ∀ (n : ℕ) → n ≤ n * n
n≤n*n (zero) = z≤n
n≤n*n (suc n) = s≤s (m≤m+n n (n * suc n))

0<2 : 0 < 2
0<2 = s≤s z≤n

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n)
  rewrite *-distribʳ-+ 2 n (sum (downFrom n))
        | sum-downFrom n
        | *-distribˡ-∸ n n 1
        | *-identityʳ n
        | sym (+-∸-assoc (n * 2) (n≤n*n n))
        | +-comm (n * 2) (n * n)
        | +-comm n (n * n)
        | +-∸-assoc (n * n) (m≤m*n n 0<2)
        | *-comm n 2
        | m+n∸m≡n n (n + 0)
        | +-identityʳ n
  = refl

-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc     : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid = record { assoc = +-assoc ; identityˡ = +-identityˡ ; identityʳ = +-identityʳ }

*-monoid : IsMonoid _*_ 1
*-monoid = record { assoc = *-assoc ; identityˡ = *-identityˡ ; identityʳ = *-identityʳ }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid = record { assoc = ++-assoc ; identityˡ = ++-identityˡ ; identityʳ = ++-identityʳ }

foldr-monoid :
  ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite assoc ⊗-monoid x (foldr _⊗_ e xs) y
  = cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y)

foldr-monoid-++ :
  ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys
  rewrite foldr-++ _⊗_ e xs ys
  = foldr-monoid _⊗_ e ⊗-monoid xs (foldr _⊗_ e ys)

-- Foldl

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid :
  ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y = sym (identityʳ ⊗-monoid y)
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x)
        | identityˡ ⊗-monoid x
        | foldl-monoid _⊗_ e ⊗-monoid xs x
        | assoc ⊗-monoid y x (foldl _⊗_ e xs)
  = refl

foldr-monoid-foldl :
  ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x ∷ xs)
  rewrite identityˡ ⊗-monoid x
        | foldl-monoid _⊗_ e ⊗-monoid xs x
  = cong (x ⊗_) (foldr-monoid-foldl _⊗_ e ⊗-monoid xs)

-- All

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x      → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ first-ℕ 93
_ = here refl

not-in : 1 ∉ first-ℕ 1
not-in (here ())
not-in (there ())

-- All and append

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record { to = to xs ys ; from = from xs ys }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
    to [] _ Pys = ⟨ [] , Pys ⟩
    to (_ ∷ xs) ys (Px ∷ P++) with to xs ys P++
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (All P xs × All P ys) → All P (xs ++ ys)
    from [] _ ⟨ _ , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- Exercise Any-++-⇔

open import Data.Sum using (_⊎_)
open _⊎_

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record { to = to xs ys ; from = from xs ys }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] _ P++ = inj₂ P++
    to (_ ∷ _) _ (here Px) = inj₁ (here Px)
    to (_ ∷ xs) ys (there P++) with to xs ys P++
    ... | inj₁ Pxs = inj₁ (there Pxs)
    ... | inj₂ Pys = inj₂ Pys
    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] _ (inj₂ Pys) = Pys
    from _  _ (inj₁ (here Px)) = here Px
    from (_ ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
    from (_ ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

∈-++ : ∀ {A : Set} {x : A} (xs ys : List A) → (x ∈ (xs ++ ys)) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++ = Any-++-⇔

-- Exercise All-++-≃

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys =
  record
    { to = to′ xs ys
    ; from = from′ xs ys
    ; from∘to = ft-identity xs ys
    ; to∘from = tf-identity xs ys
    }
      where
        to′ : ∀ (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
        to′ [] _ Pys = ⟨ [] , Pys ⟩
        to′ (_ ∷ xs) ys (Px ∷ P++) with to′ xs ys P++
        ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

        from′ : ∀ (xs ys : List A) → (All P xs × All P ys) → All P (xs ++ ys)
        from′ [] _ ⟨ _ , Pys ⟩ = Pys
        from′ (_ ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from′ xs ys ⟨ Pxs , Pys ⟩

        ft-identity : ∀ (xs ys : List A) (p++ : All P (xs ++ ys)) → from′ xs ys (to′ xs ys p++) ≡ p++
        ft-identity [] _ _ = refl
        ft-identity (_ ∷ xs) ys (Px ∷ P++) = cong (Px ∷_) (ft-identity xs ys P++)

        tf-identity : ∀ (xs ys : List A) (p× : All P xs × All P ys) → to′ xs ys (from′ xs ys p×) ≡ p×
        tf-identity [] _ ⟨ [] , _ ⟩ = refl
        tf-identity (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ rewrite tf-identity xs ys ⟨ Pxs , Pys ⟩ = refl

-- Exercise ¬Any≃All¬

open import Data.Empty using (⊥; ⊥-elim)

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any⇔All¬ {A} {P} xs =
  record
    { to = to′ xs
    ; from = from′ xs
    ; from∘to = ft-identity
    ; to∘from = tf-identity
    }
    where
      to′ : ∀ (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
      to′ [] ¬Any = []
      to′ (_ ∷ xs) ¬Any = (¬Any ∘ here) ∷ to′ xs (¬Any ∘ there)
      from′ : ∀ (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
      from′ _ (¬P ∷ _) (here Px) = ¬P Px
      from′ (_ ∷ xs) (_ ∷ All¬) (there Anyxs) = from′ xs All¬ Anyxs
      ft-identity : ∀ {xs : List A} (x : (¬_ ∘ Any P) xs) → from′ xs (to′ xs x) ≡ x
      ft-identity ¬Any = extensionality (⊥-elim ∘ ¬Any)
      tf-identity : ∀ {xs : List A} (x : All (¬_ ∘ P) xs) → to′ xs (from′ xs x) ≡ x
      tf-identity [] = refl
      tf-identity (¬Px ∷ All¬) = cong (¬Px ∷_) (tf-identity All¬)

-- All-∀

-- All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → (All P xs) ≃ (∀ {x : A} → x ∈ xs → P x)
-- All-∀ {A} {P} xs =
--   record
--     { to = to′ xs
--     ; from = from′ xs
--     ; from∘to = ft-identity xs
--     ; to∘from = {!   !}
--     }
--     where
--       to′ : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs → (∀ {x : A} → x ∈ xs → P x)
--       to′ _ (x ∷ _) (here refl) = x
--       to′ (_ ∷ xs) (_ ∷ Pxs) (there x∈xs) = to′ xs Pxs x∈xs
--       from′ : ∀ {A : Set} {P : A → Set} (xs : List A) → (∀ {x : A} → x ∈ xs → P x) → (All P xs)
--       from′ [] ∀∈ = []
--       from′ (_ ∷ xs) ∀∈ = ∀∈ (here refl) ∷ from′ xs (∀∈ ∘ there)
--       ft-identity : ∀ {A : Set} {P : A → Set} (xs : List A) (x : All P xs) → from′ xs (to′ xs x) ≡ x
--       ft-identity _ [] = refl
--       ft-identity (_ ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (ft-identity xs Pxs)
--       tf-identity : ∀ {A : Set} {P : A → Set} (xs : List A) (y : {x : A} → x ∈ xs → P x) → to′ xs (from′ xs y) ≡ y
--       tf-identity = {!   !}
