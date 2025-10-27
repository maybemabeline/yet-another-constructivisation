module deduction-properties where

open import base
open import formula
open import deduction

open Σ

-- Syntactic properties of the classical calculus

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


weaken : {Γ Δ : Context} {B : Formula}
        → Δ ≡ B ∷ Γ
        → CL⊢ Γ
        → CL⊢ Δ
weaken f (atom-elim e d Π) = atom-elim (≡lemma2 f e) d (weaken ≡refl Π)
weaken f (atom-intro e d Πs) = atom-intro (≡lemma f e) d (λ x → weaken (≡trans (≡cons f) ≡swap) (Πs x))
weaken f (neg-atom-intro e m) = neg-atom-intro (≡lemma f e) (there m)
weaken f (foral-intro e Πs) = foral-intro (≡lemma f e) (λ x → weaken ≡swap (Πs x))
weaken f (exists-intro t e Π) = exists-intro t (≡lemma f e) (weaken (≡trans (≡cons f) ≡swap) Π)

lem : (A : Formula) → CL⊢ (A ∨ neg A)
lem (atom a) = neg-atom-intro ≡swap here
lem (neg-atom a) = neg-atom-intro ≡refl here
lem (exists A) = foral-intro ≡swap (λ x → exists-intro x ≡swap (weaken ≡cycle2 (lem (A x))))
lem (foral A) = foral-intro ≡refl (λ x → exists-intro x ≡swap (weaken (≡trans ≡swap ≡cycle2) (lem (A x))))

-- Soundness of the intuitionistic calculus


lemma : {n : ℕ} {Γ : Context} {A : Fin n → Formula}
      → ((x : Fin n) → ⟦ A x ∷ Γ ⟧c)
      → ((x : Fin n) → ⟦ A x ⟧) + ⟦ Γ ⟧c
lemma {zero} f = inl (λ ())
lemma {succ n} f with f zero
... | here p with lemma (λ x → f (succ x))
...   | inl q = inl λ { zero → p ; (succ x) → q x}
...   | inr q = inr q
lemma {succ n} f | (there p) = inr p

soundness : {Γ : Context} → IL⊢ Γ → ⟦ Γ ⟧c
soundness (atom-elim e d Π) with subst (e .fst) (soundness Π)
... | here (atom p) = ex-falso (atom-sound-false d p)
... | there p = p
soundness (atom-intro e d Πs) with (lemma (λ x → (soundness (Πs x))))
... | inl H = subst (e .snd) (here (atom (atom-sound-true d (λ x → match (H x) wth λ { (atom K) → K}))))
... | inr H = H
soundness (neg-atom-intro {a = a} e m) with Atom-dec a
... | inl H = subst (e .snd) (there (inc m (atom H)))
... | inr H = subst (e .snd) (here (neg-atom H))
soundness (foral-intro e Πs) with (lemma (λ x → (soundness (Πs x))))
... | inl H = subst (e .snd) (here (foral H))
... | inr H = subst (e .snd) (there H)
soundness (exists-intro t e Π) with soundness Π
... | here H = subst (e .snd) (here (exists (t , H)))
... | there H = H
