module test where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

-- Proposition on (n:ℕ), where n is an even
data _even : ℕ → Set where
  -- zero is always even
  ZERO : zero even
  -- Given an x:ℕ and a proof that x is even,
  -- (x + 2) is even
  STEP : ∀ x → x even → suc (suc x) even

-- using C-c C-r for proof start
-- usring C-c C-s for `auto-solve`
fourIsEven₁ : suc(suc(suc(suc zero))) even
fourIsEven₁ = STEP (suc (suc zero)) (STEP zero ZERO)

-- Using an implicit argument for STEP
data _even₂ : ℕ → Set where
  ZERO : zero even₂
  STEP : ∀ {x} → x even₂ → suc (suc x) even₂

-- Proving an implicit proposition
fourIsEven₂ : suc(suc(suc(suc zero))) even₂
fourIsEven₂ = STEP (STEP ZERO)
-- Manually
fourIsEven₃ : suc(suc(suc(suc zero))) even₂
fourIsEven₃ = STEP {suc(suc zero)} (STEP {zero} ZERO)

-- Conjunction Data-type (Prop)
-- Some logical connectives
data _∧_ (P Q : Set) : Set where
  conj : P → Q → (P ∧ Q)

_⇔_ : (P Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)

∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm' (conj p q) = (conj q p)

-- commutativity of ∧ proof
∧-comm : {P Q : Set} → (P ∧ Q → Q ∧ P) ∧ (Q ∧ P → P ∧ Q)
∧-comm = conj ∧-comm' ∧-comm'

-- associativity of ∧ proof
∧-assoc₁ : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (conj (conj p q) r) = conj p (conj q r)

∧-assoc₂ : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (conj p (conj q r)) = conj (conj p q) r

∧-assoc : {P Q R : Set} → ((P ∧ Q) ∧ R) ⇔ (P ∧ (Q ∧ R))
∧-assoc = conj ∧-assoc₁ ∧-assoc₂

data _∨_ (P Q : Set) : Set where
  inl : P → (P ∨ Q)
  inr : Q → (P ∨ Q)

-- commutativity of ∨ proof
∨-comm' : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm' (inl p) = inr p
∨-comm' (inr q) = inl q

∨-comm : {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = conj ∨-comm' ∨-comm'

-- associativity of ∧ proof
∨-assoc₁ : {P Q R : Set} → ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))
∨-assoc₁ (inl (inl p)) = inl p
∨-assoc₁ (inl (inr q)) = inr (inl q)
∨-assoc₁ (inr r) = inr (inr r)

∨-assoc₂ : {P Q R : Set} → (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)
∨-assoc₂ (inl p) = inl (inl p)
∨-assoc₂ (inr (inl q)) = inl (inr q)
∨-assoc₂ (inr (inr r)) = inr r

v-assoc : {P Q R : Set} → ((P ∨ Q) ∨ R) ⇔ (P ∨ (Q ∨ R))
v-assoc = conj ∨-assoc₁ ∨-assoc₂

-- The beginning of negation
data ⊥ : Set where

¬ : Set -> Set
¬ A = A → ⊥

-- record Σ (A : Set) (B : A → Set) : Set
-- record Σ {A : Set} (x : A) (B : A → Set) : Set where
--   constructor _,_
--   field fst : A
--         snd : B fst

data Σ (A : Set) (B : A → Set) : Set where
  pair : (x : A) → (B x) → Σ A B

-- Quanitifier Negation
quantifierNegation : {A : Set} → {x : A} → {B : A → Set} → (Σ A ¬(B)) → ¬(∀ x → B)
quantifierNegation = ?
