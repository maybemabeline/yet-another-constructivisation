open import Agda.Primitive

_∘_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
    → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

match_wth : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A → (A → B) → B
match x wth f = f x

data Id {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : {a : A} → Id a a

-- Negation and decidability

data ⊥ : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

ex-falso : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
ex-falso ()

data _+_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl : A → A + B
  inr : B → A + B

infixr 20 _+_

decidable : Set → Set
decidable A = A + ¬ A

-- Sigma types

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

_×_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

-- Natural numbers and finite types

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)

sing : {ℓ : Level} {A : Set ℓ} (a : A) → Fin 1 → A
sing a zero = a

empty : {ℓ : Level} {A : Set ℓ} → Fin 0 → A
empty ()

ι : ∀ {n : ℕ} → Fin n → ℕ
ι zero = zero
ι (succ x) = succ (ι x)

data countable : Set → Set where
  finite : ∀ {n : ℕ} → countable (Fin n)
  infinite : countable ℕ

-- List

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → List A → List A

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → List A → List B
map f [] = []
map f (x ∷ l) = f x ∷ map f l

infixr 22 _∷_

module _ {ℓ} {A : Set ℓ} where

  [_] : A → List A
  [ a ] = a ∷ []

  data _∈_ : A → List A → Set ℓ where
    here : ∀ {x : A} {l : List A} → x ∈ x ∷ l
    there : ∀ {x y : A} {l : List A} → x ∈ l → x ∈ y ∷ l

  infix 21 _∈_

  _⊂_ : List A → List A → Set ℓ
  u ⊂ v = ∀ {x : A} → x ∈ u → x ∈ v

  _≡_ : List A → List A → Set ℓ
  u ≡ v = (u ⊂ v) × (v ⊂ u)

  infixr 21 _≡_
  infixr 21 _⊂_

  ≡mem : {x y : A} {l : List A} → y ∷ l ⊂ [ x ] → (Id x y)
  ≡mem e with (e here)
  ... | here = refl

  ≡cons-one : {x : A} {u v : List A}
             → u ⊂ x ∷ v
             → x ∈ u + u ⊂ v
  ≡cons-one {u = []} s = inr (λ ())
  ≡cons-one {u = x ∷ u} s with (s here)
  ... | here = inl here
  ... | there p with ≡cons-one (λ m → s (there m))
  ...   | inl q = inl (there q)
  ...   | inr q = inr (λ { here → p ; (there m) → q m})

  -- ≡cons-cons : {x y : A} {u v : List A}
  --            → x ∷ u ≡ y ∷ v
  --            → Id x y × u ≡ v
  -- ≡cons-cons (s , t) with ≡cons-one s
  -- ... | inl here = {!!}
  -- ... | inl (there m) = {!!}
  -- ... | inr f = {!!}



  ≡nil : {x : A} {u : List A} → ¬ (x ∷ u ⊂ [])
  ≡nil s with s here
  ... | ()


  ⊂trans : {u v w : List A} → u ⊂ v → v ⊂ w → u ⊂ w
  ⊂trans s t m = t (s m)

  ≡trans : {u v w : List A} → u ≡ v → v ≡ w → u ≡ w
  ≡trans (s , t) (s' , t') = (s' ∘ s) , (t ∘ t')

  ≡refl : {u : List A} → u ≡ u
  ≡refl = (λ m → m) , (λ m → m)

  ≡symm : {u v : List A} → u ≡ v → v ≡ u
  ≡symm (s , t) = t , s

  ⊂swap : {x y : A} {l : List A} → y ∷ x ∷ l ⊂ x ∷ y ∷ l
  ⊂swap here = there here
  ⊂swap (there here) = here
  ⊂swap (there (there m)) = there (there m)

  ≡swap : {x y : A} {l : List A} → y ∷ x ∷ l ≡ x ∷ y ∷ l
  ≡swap = ⊂swap , ⊂swap

  ⊂cycle : {x y z : A} {l : List A} → z ∷ x ∷ y ∷ l ⊂ x ∷ y ∷ z ∷ l
  ⊂cycle here = there (there here)
  ⊂cycle (there here) = here
  ⊂cycle (there (there here)) = there here
  ⊂cycle (there (there (there m))) = there (there (there m))

  ≡cycle : {x y z : A} {l : List A} → z ∷ x ∷ y ∷ l ≡ x ∷ y ∷ z ∷ l
  ≡cycle = ⊂cycle , (⊂trans ⊂cycle ⊂cycle)

  ≡cycle2 : {x y z : A} {l : List A} → y ∷ z ∷ x ∷ l ≡ x ∷ y ∷ z ∷ l
  ≡cycle2 = ≡trans ≡cycle ≡cycle

  ⊂cons : {x : A} {u v : List A} → u ⊂ v → x ∷ u ⊂ x ∷ v
  ⊂cons s here = here
  ⊂cons s (there m) = there (s m)

  ≡cons : {x : A} {u v : List A} → u ≡ v → x ∷ u ≡ x ∷ v
  ≡cons (s , t) = (⊂cons s) , (⊂cons t)

  data All {ℓ'} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
    nil : All P []
    cons : {x : A} {l : List A} → P x → All P l → All P (x ∷ l)

mapAll : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ''} {f : A → B} {l : List A}
           {P : A → Set ℓ'} {Q : B → Set ℓ'}
       → (∀ {x : A} → P x → Q (f x))
       → All P l → All Q (map f l)
mapAll f nil = nil
mapAll f (cons p l) = cons (f p) (mapAll f l)

  -- somethingAll : ∀ {ℓ'} {l : List A} {P : A → Set ℓ'}
  --              → All P l



-- All-sing : ∀ {ℓ'} {P : A → Set ℓ'} {x : A} → All P [ x ] → P x
-- All-sing (cons nil p) = p

-- Maybe

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  None : Maybe A
  Some : A → Maybe A
