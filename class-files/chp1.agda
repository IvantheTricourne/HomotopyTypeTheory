module chp1 where

-- Chapter 1 in Hott

-- **How to introduce types**
-- Constructors -- introduction rule
-- Destructors  -- elimination rule (rec and ind)
-- Computation  -- how destructors interact with constructors

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Big C is for relevance of proof (C : Set)
                             -- ℕ is n, C is result of rec on n, C is the answer
recℕ : (C : Set) → (c : C) → (f : (ℕ → C → C)) → ℕ → C
recℕ C c f zero = c
recℕ C c f (succ n) = f n (recℕ C c f n)

double : ℕ → ℕ
double = recℕ ℕ zero (λ n r → succ (succ r))

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r → λ n → succ (r n))

mul : ℕ → ℕ → ℕ
mul = recℕ (ℕ → ℕ) (λ n → zero) (λ m r → λ n → add m (r n))

-- fact : ℕ → ℕ
-- fact = recℕ 1 (λ n r → suc n * r)

indℕ : (C : ℕ → Set) → (proof₀ : C zero) → (proof₁ : ((n : ℕ) → C n → C (succ n))) → (n : ℕ) → C n
indℕ C c f zero = c
indℕ C c f (succ n) = f n (indℕ C c f n)

-- add-assoc : (i j k : ℕ) → add i (add j k) ≡ add (add i j) k
-- add-assoc = indℕ
--             (λ i → (j k : ℕ) → add i (add j k) ≡ add (add i j) k)
               -- perform case-split on `i`, give me back some type
--             (λ j k → refl) -- base case
--             (λ i i+[j+k]≡[i+j]+k j k → cong succ (i+[j+k]≡[i+j]+k j k)) -- yeah...

-- **Properties of Identity types**
-- cong == congruence
-- sym  == symmetry
-- refl == reflexivity

