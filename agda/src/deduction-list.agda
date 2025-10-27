module deduction-list where

open import base
open import formula

postulate _⊢_ : List Atom → Maybe Atom → Set

data CL⊢ : Context → Set₁ where

  atom-elim : {a : Atom} {Γ Δ : Context}
            → Δ ≡ (atom a ∷ Γ)
            → CL⊢ Δ
            → [ a ] ⊢ None
            → CL⊢ Γ

  atom-intro : {l : List Atom} {a : Atom} {Γ Δ : Context}
             → Δ ≡ atom a ∷ Γ
             → All CL⊢ (map (λ x → atom x ∷ Δ) l)
             → l ⊢ Some a
             → CL⊢ Δ

  neg-atom-intro : {a : Atom} {Γ Δ : Context}
                 → Δ ≡ (neg-atom a ∷ Γ)
                 → (atom a) ∈ Γ
                 → CL⊢ Δ

  foral-intro : {I : Set} {A : I → Formula} {Γ Δ : Context}
              → Δ ≡ foral A ∷ Γ
              → (∀ (x : I) → CL⊢ (A x ∷ Γ))
              → CL⊢ Δ

  exists-intro : {I : Set} {A : I → Formula} {Γ Δ : Context} (t : I)
               → Δ ≡ (exists A) ∷ Γ
               → CL⊢ (A t ∷ Δ)
               → CL⊢ Δ


weaken : {Γ Δ : Context} {B : Formula}
       → Δ ≡ B ∷ Γ
       → CL⊢ Γ
       → CL⊢ Δ

weaken-list : {L : List Context} {B : Formula}
            → All CL⊢ L
            → All (λ Γ → {Δ : Context} → Δ ≡ B ∷ Γ → CL⊢ Δ) L

≡lemma : {Γ Δ Θ : Context} {B C : Formula}
       → Δ ≡ B ∷ Γ
       → Γ ≡ C ∷ Θ
       → Δ ≡ C ∷ B ∷ Θ
≡lemma f e = ≡trans f (≡trans (≡cons e) ≡swap)

≡lemma2 : {Γ Δ Θ : Context} {B C : Formula}
        → Δ ≡ B ∷ Γ
        → Θ ≡ C ∷ Γ
        → (B ∷ Θ) ≡ (C ∷ Δ)
≡lemma2 f e = ≡trans (≡cons e) (≡trans ≡swap (≡cons (≡symm f)))

weaken f (atom-elim e Π d) = atom-elim (≡lemma2 f e) (weaken ≡refl Π) d
weaken {Γ} {Δ} {B} f (atom-intro e Πs d) = atom-intro (≡lemma f e) (lemma (weaken-list Πs)) d
  where

  lemma : {l : List Atom}
        → All (λ Γ' → {Θ : Context} → Θ ≡ B ∷ Γ' → CL⊢ Θ) (map (λ x → atom x ∷ Γ) l)
        → All CL⊢ (map (λ x → atom x ∷ Δ) l)
  lemma {l = []} nil = nil
  lemma {l = x ∷ l} (cons p H) = cons (p (≡trans (≡cons f) ≡swap)) (lemma H)

weaken f (neg-atom-intro e m) = neg-atom-intro (≡lemma f e) (there m)
weaken f (foral-intro e Πs) = foral-intro (≡lemma f e) (λ x → weaken ≡swap (Πs x))
weaken f (exists-intro t e Π) = exists-intro t (≡lemma f e) (weaken (≡trans (≡cons f) ≡swap) Π)

weaken-list nil = nil
weaken-list (cons Π H) = cons (λ f → weaken f Π) (weaken-list H)


lem : (A : Formula) → CL⊢ (A ∨ neg A)
lem (atom a) = neg-atom-intro ≡swap here
lem (neg-atom a) = neg-atom-intro ≡refl here
lem (exists A) = foral-intro ≡swap (λ x → exists-intro x ≡swap (weaken ≡cycle2 (lem (A x))))
lem (foral A) = foral-intro ≡refl (λ x → exists-intro x ≡swap (weaken (≡trans ≡swap ≡cycle2) (lem (A x))))

data IL⊢_ : Context → Set₁ where

  atom-elim : {a : Atom} {Γ : Context}
            → IL⊢ (atom a ∷ Γ) → [ a ] ⊢ None
            → IL⊢ Γ

  atom-intro : {l : List Atom} {a : Atom} {Γ : Context}
             → All (λ x → IL⊢ (atom x ∷ atom a ∷ Γ)) l
             → l ⊢ Some a
             → IL⊢ (atom a ∷ Γ)

  neg-atom-intro : {a : Atom} {Γ : Context}
                 → atom a ∈ Γ → IL⊢ (neg-atom a ∷ Γ)

  foral-intro : {n : ℕ} {A : Fin n → Formula} {Γ : Context}
              → (∀ (x : Fin n) → IL⊢ (A x ∷ Γ))
              → IL⊢ (foral A ∷ Γ)

  exists-intro : {I : Set} {A : I → Formula} {Γ : Context} (t : I)
               → IL⊢ (A t ∷ exists A ∷ Γ)
               → IL⊢ (exists A ∷ Γ)
