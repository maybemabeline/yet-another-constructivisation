module deduction where

open import base
open import formula

postulate _⊢_ : {n : ℕ} → (Fin n → Atom) → Maybe Atom → Set

module _ {n : ℕ} {l : Fin n → Atom} {a : Atom} where

  postulate atom-complete-true : (∀ (x : Fin n) → Atom-true (l x) → Atom-true a) → l ⊢ Some a
  postulate atom-sound-true : l ⊢ Some a → (∀ (x : Fin n) → Atom-true (l x)) → Atom-true a

postulate atom-complete-false : {a : Atom} → ¬ (Atom-true a) → sing a ⊢ None
postulate atom-sound-false : {a : Atom} → sing a ⊢ None → ¬ (Atom-true a)

data CL⊢ : Context → Set₁ where

  atom-elim : {a : Atom} {Γ Δ : Context}
            → Δ ≡ (atom a ∷ Γ)
            → sing a ⊢ None
            → CL⊢ Δ
            → CL⊢ Γ

  atom-intro : {n : ℕ} {l : Fin n → Atom} {a : Atom} {Γ Δ : Context}
             → Δ ≡ atom a ∷ Γ
             → l ⊢ Some a
             → (∀ (x : Fin n) → CL⊢ ((atom (l x)) ∷ Δ))
             → CL⊢ Δ

  neg-atom-intro : {a : Atom} {Γ Δ : Context}
                 → Δ ≡ (neg-atom a ∷ Γ)
                 → (atom a) ∈ Γ
                 → CL⊢ Δ

  foral-intro : {I : Set} {A : I → Formula} {Γ Δ : Context}
              → Δ ≡ (foral A) ∷ Γ
              → (∀ (x : I) → CL⊢ (A x ∷ Γ))
              → CL⊢ Δ

  exists-intro : {I : Set} {A : I → Formula} {Γ Δ : Context} (t : I)
               → Δ ≡ (exists A) ∷ Γ
               → CL⊢ (A t ∷ Δ)
               → CL⊢ Δ

data IL⊢ : Context → Set₁ where

  atom-elim : {a : Atom} {Γ Δ : Context}
            → Δ ≡ (atom a ∷ Γ)
            → sing a ⊢ None
            → IL⊢ Δ
            → IL⊢ Γ

  atom-intro : {n : ℕ} {l : Fin n → Atom} {a : Atom} {Γ Δ : Context}
             → Δ ≡ atom a ∷ Γ
             → l ⊢ Some a
             → (∀ (x : Fin n) → IL⊢ ((atom (l x)) ∷ Δ))
             → IL⊢ Δ

  neg-atom-intro : {a : Atom} {Γ Δ : Context}
                 → Δ ≡ (neg-atom a ∷ Γ)
                 → (atom a) ∈ Γ
                 → IL⊢ Δ

  foral-intro : {n : ℕ} {A : Fin n → Formula} {Γ Δ : Context}
              → Δ ≡ (foral A) ∷ Γ
              → (∀ (x : Fin n) → IL⊢ (A x ∷ Γ))
              → IL⊢ Δ

  exists-intro : {I : Set} {A : I → Formula} {Γ Δ : Context} (t : I)
               → Δ ≡ (exists A) ∷ Γ
               → IL⊢ (A t ∷ Δ)
               → IL⊢ Δ
