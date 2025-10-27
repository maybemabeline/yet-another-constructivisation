module formula where

open import base
open Σ

postulate Atom : Set
postulate Atom-true : Atom → Set
postulate Atom-dec : ∀ (a : Atom) → decidable (Atom-true a)

data Formula : Set₁ where
  atom : Atom → Formula
  neg-atom : Atom → Formula
  exists : {I : Set} → (I → Formula) → Formula
  foral : {I : Set} → (I → Formula) → Formula

neg : Formula → Formula
neg (atom a) = neg-atom a
neg (neg-atom a) = atom a
neg (exists A) = foral (λ x → neg (A x))
neg (foral A) = exists (λ x → neg (A x))

Context = List Formula

_∨_ : Formula → Formula → Context
A ∨ B = A ∷ B ∷ []

data ⟦_⟧ : Formula → Set₁ where
  atom : {a : Atom} → Atom-true a → ⟦ atom a ⟧

  neg-atom : {a : Atom} → ¬ (Atom-true a) → ⟦ neg-atom a ⟧

  exists : {I : Set} {A : I → Formula}
         → Σ I (λ x → ⟦ A x ⟧) → ⟦ exists A ⟧

  foral : {I : Set} {A : I → Formula}
        → (∀ (x : I) → ⟦ A x ⟧) → ⟦ foral A ⟧

data ⟦_⟧c : Context → Set₁ where
  here : {A : Formula} {Γ : Context} → ⟦ A ⟧ → ⟦ A ∷ Γ ⟧c
  there : {A : Formula} {Γ : Context} → ⟦ Γ ⟧c → ⟦ A ∷ Γ ⟧c

inc : {A : Formula} {Γ : Context} → A ∈ Γ → ⟦ A ⟧ → ⟦ Γ ⟧c
inc here p = here p
inc (there m) p = there (inc m p)

subst : {Γ Δ : Context} → Γ ⊂ Δ → ⟦ Γ ⟧c → ⟦ Δ ⟧c
subst e (here q) = inc (e here) q
subst e (there p) = subst (λ x → e (there x)) p

data _↝_ : Formula → Formula → Set₁ where
  atom : {a : Atom} → (atom a) ↝ (atom a)

  neg-atom : {a : Atom} → (neg-atom a) ↝ (neg-atom a)

  exists : {I : Set} {A A' : I → Formula}
         → (∀ (x : I) → (A x) ↝ (A' x))
         → (exists A) ↝ (exists A')

  foral : {I : Set} {A A' : I → Formula} {n : ℕ} (ι : Fin n → I)
        → (∀ (x : I) → (A x) ↝ (A' x))
        → (foral A) ↝ (foral (A' ∘ ι))

data _↝c_ : Context → Context → Set₁ where
  nil : [] ↝c []
  cons : ∀ {A A' : Formula} {Γ Γ' Δ Δ' : Context}
       → A ↝ A' → Γ ↝c Γ'
       → A ∷ Γ ≡ Δ → A' ∷ Γ' ≡ Δ'
       → Δ ↝c Δ'

-- ≡simulation : {Γ Γ' Δ : Context}
--             → Γ ≡ Δ → SimulationContext Γ Γ'
--             → Σ Context (SimulationContext Δ)
-- ≡simulation {Δ = []} e nil = [] , nil
-- ≡simulation {Δ = A ∷ Δ} e nil = ex-falso (≡nil (e .snd))
-- ≡simulation {Δ = []} e (cons σ Σ) = ex-falso (≡nil (e .fst))
-- ≡simulation {Δ = A ∷ Δ} e (cons σ Σ) = {!!}
-- ... | inl x = {!!}
-- ... | inr (inl x) = {!!}
-- ... | inr (inr f) with ≡simulation f Σ
-- ... | (Δ' , Σ') = (A ∷ Δ') , cons {!!} Σ'
