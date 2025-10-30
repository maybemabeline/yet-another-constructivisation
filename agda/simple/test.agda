data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data Atom : Set where
  leq : Nat → Nat → Atom
  le : Nat → Nat → Atom
  eq : Nat → Nat → Atom

data Formula : Set where
  atom : Atom → Formula
  negAtom : Atom → Formula
  conj : Formula → Formula → Formula
  disj : Formula → Formula → Formula
  uni : (Nat → Formula) → Formula
  exi : (Nat → Formula) → Formula

data Context : Set where
   nil : Context
   cons : Formula → Context → Context

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B


neg : Formula → Formula
neg (atom a) = negAtom a
neg (negAtom a) = atom a
neg (conj A B) = disj (neg A) (neg B)
neg (disj A B) = conj (neg A) (neg B)
neg (uni A) = exi (λ n → neg (A n))
neg (exi A) = uni (λ n → neg (A n))

data Proof : Set where
  lem : Atom → Context → Proof
  true : Atom → Context → Proof
  conj : Formula → Formula → Proof → Proof → Proof
  disj : Formula → Formula → Proof → Proof
  uni : (Nat → Formula × Proof) → Proof
  exi : Nat → Formula → Proof → Proof
  cut : Formula → Proof → Proof → Proof

test : (Nat → Nat) → Nat → Proof
test f m = exi m (uni (λ n → atom (leq zero n))) (uni (λ n → (atom (leq zero n)) , {!!}))

data SimpleProof : Set where
  lem : Atom → Context → SimpleProof
  true : Atom → Context → SimpleProof
  conj : Formula → Formula → SimpleProof → SimpleProof → SimpleProof
  disj : Formula → Formula → SimpleProof → SimpleProof
  exi : Nat → Formula → SimpleProof → SimpleProof
