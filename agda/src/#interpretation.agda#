module interpretation where

open import Agda.Primitive
open import base
open import formula
open import deduction
open Σ

ψ : (A : Formula) → Set₁
ψ A = ∀ {A' : Formula} → A ↝ A' → IL⊢ [ A' ]

soundness : {A : Formula} → CL⊢ [ A ] → ψ A
soundness (atom-elim x x₁ Π) σ = {!!}
soundness (atom-intro x x₁ x₂) σ = {!!}
soundness (neg-atom-intro x x₁) σ = {!!}
soundness (foral-intro e Πs) σ with ≡mem (e .snd)
soundness (foral-intro e Πs) (foral ι σ) | refl = foral-intro {!!} {!!}
soundness (exists-intro t e Π) σ with ≡mem (e .snd)
soundness (exists-intro t e Π) (exists σ) | refl = exists-intro t {!!} {!!}


something : {Γ Γ' : Context} → CL⊢ Γ → Γ ↝c Γ' → IL⊢ Γ'
something (atom-elim x x₁ Π) σ = {!!}
something (atom-intro x x₁ x₂) σ = {!!}
something (neg-atom-intro x x₁) σ = {!!}
something (foral-intro e Πs) σ = {!!}
something (exists-intro t e Π) nil with (e .snd here)
... | ()
something (exists-intro t e Π) (cons σ Σ f g) = {!!}


-- data Tree {ℓ ℓ' ℓ''} (A : Set ℓ) (B : A → Set ℓ') (C : Set ℓ'') : Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
--   leaf : C → Tree A B C
--   branch : (x : A) → (B x → Tree A B C) → Tree A B C

-- traverse : {A : Set} {B : A → Set} {C : Set}
--          → Tree A B C
--          → ((x : A) → B x) → C
-- traverse (leaf c) f = c
-- traverse (branch a b) f = traverse (b (f a)) f

data 


-- test : Formula → Tree Set (λ I → {n : ℕ} → Fin n → I) Atom
-- test (atom x) = leaf x
-- test (neg-atom x) = leaf x
-- test (exists A) = {!!}
-- test (foral A) = {!!}

-- data BranchingFormula : Set₁ where
--   atom : Atom → BranchingFormula
--   neg-atom : Atom → BranchingFormula
--   exists : {I : Set} → (I → BranchingFormula) → BranchingFormula
--   foral : {I : Set} → (I → BranchingFormula)


module DependentTree where

  traverse
