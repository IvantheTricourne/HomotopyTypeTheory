module hw1 where

open import Data.Nat using (ℕ; suc)
open import Data.Empty

-- My Prelude
data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

rec≡ : {A : Set} →
       (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl y) = reflR {y}

J : {A : Set} →
    (R : {x y : A} → (p : x ≡ y) → Set)
    (r : (a : A) → R (refl a)) →
    ({a b : A} (p : a ≡ b) → R p)
J R r (refl y) = r y

PHJ : {A : Set} →
      {a : A} (R : (a' : A) (p : a ≡ a') → Set)
      (r : R a (refl a))
      {a' : A} (p : a ≡ a') → R a' p
PHJ R r (refl a) = r

PHJ' : {A : Set} →
       {a : A} (R : (a' : A) (p : a' ≡ a) → Set)
       (r : R a (refl a))
       {a' : A} (p : a' ≡ a) → R a' p
PHJ' R r (refl a) = r

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = J (λ {x} {y} x≡y → y ≡ x)
        (λ a → refl a)

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f = J (λ {x} {y} x≡y → f x ≡ f y)
           (λ a → refl (f a))

trans' : {A : Set} {x y z : A} → x ≡ y → (∀ z → y ≡ z → x ≡ z)
trans' = J (λ {x} {y} p → (∀ z → y ≡ z → x ≡ z))
           (λ a z a≡z → a≡z)

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = λ {A} {x y z} x≡y y≡z → trans' {A} {x} {y} {z} x≡y z y≡z

recℕ : (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ C c f 0       = c
recℕ C c f (suc n) = f n (recℕ C c f n)

indℕ : (C : ℕ → Set) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C c f 0       = c
indℕ C c f (suc n) = f n (indℕ C c f n)

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r n → suc (r n))

mul : ℕ → ℕ → ℕ
mul = recℕ (ℕ → ℕ) (λ _ → 0) (λ _ r n → add n (r n))

exp : ℕ → ℕ → ℕ
exp m = recℕ ℕ 1 (λ _ ans → mul m ans)

data _×_ (A B : Set) : Set where
  _,_ : A → B → (A × B)

proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (a , b) = b

rec× : {A B C : Set} (g : A → B → C) → A × B → C
rec× = λ g x → g (proj₁ x) (proj₂ x)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

rec+ : {A B C : Set} → (A → C) → (B → C) → A + B → C
rec+ a→c b→c (inl a) = a→c a
rec+ a→c b→c (inr b) = b→c b

record Σ (A : Set) (B : A → Set) : Set
record Σ A B where
  constructor _,_
  field fst : A
        snd : B fst
open Σ

recΣ : {A C : Set} {B : A → Set} (g : (x : A) → B x → C) → Σ A B → C
recΣ = λ g x → g (fst x) (snd x)

¬ : Set → Set
¬ A = A → ⊥

data Two : Set where
  0₂ : Two
  1₂ : Two

rec₂ : (C : Set) → C → C → Two → C
rec₂ C c₁ c₂ 0₂ = c₁
rec₂ C c₁ c₂ 1₂ = c₂


-- Ex1.1 Given functions f : A → B and g : B → C, define their composite
-- g ◦ f : A → C. Show that we have h ◦ (g ◦ f ) ≡ (h ◦ g) ◦ f .
_⋆_ : {A B C : Set} → (A → B) → (B → C) → A → C
_⋆_ f g = λ a → g (f a)

assoc⋆ : {A B C D : Set} (f : C → D) (g : B → C) (h : A → B) →
         (h ⋆ (g ⋆ f)) ≡ ((h ⋆ g) ⋆ f)
assoc⋆ f g h = refl (λ a → f (g (h a)))

-- Ex1.2 Derive the recursion principle for products recA×B using only
-- the projections, and verify that the definitional equalities are valid.
-- Do the same for Σ-types.

-- proj×Def≡ : {!!}
-- proj×Def≡ = {!!}

-- projΣDef≡ : {!!}
-- projΣDef≡ = {!!}


-- Ex1.3 Derive the induction principle for products indA×B, using only
-- the projections and the propositional uniqueness principle uppt. Verify
-- that the definitional equalities are valid. Generalize uppt to Σ-types,
-- and do the same for Σ-types. (This requires concepts from Chapter 2.)
uppt : {A B : Set} → (x : A × B) → ((proj₁ x) , (proj₂ x)) ≡ x
uppt (a , b) = refl (a , b)

-- cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y

-- I have ->  g (proj₁ x) (proj₂ x) : C ((proj₁ x) , (proj₂ x))
--            uppt x : ((proj₁ x) , (proj₂ x)) ≡ x
-- prove C x

ind× : {A B : Set} {C : A × B → Set} (g : (a : A) (b : B) → C (a , b)) →
       (x : A × B) → C x
ind× {A} {B} {C} = λ g x → {!!}

-- Ex1.4
iter : {C : Set} → C → (C → C) → ℕ → C
iter c c→c 0       = c
iter c c→c (suc n) = c→c (iter c c→c n)

iterRecℕ : {C : Set} → C → (ℕ → C → C) → ℕ → C
iterRecℕ c s = λ n → iter c (s n) n

-- Ex1.5
-- Define A + B = Σ(x:2) rec2(Set,A,B,x)

-- _+_ : (A B : Set) (x : Two) → Σ Two (rec₂ Set A B x)
-- _+_ = ?

-- Ex1.6
-- requires `function extensionality axiom`

-- Ex1.7
-- Ex1.8
-- mul and exp are defined above
Semiring[ℕ+×01] : (x y z : ℕ) → ((add x 0 ≡ x) ×

-- Ex1.9 Derive Fin and fmax
data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)

fmax : (n : ℕ) → Fin (suc n)
fmax = indℕ (λ n → Fin (suc n)) fz (λ _ r → fs r) 

-- Ex1.10
ackPat : ℕ → ℕ → ℕ
ackPat 0 n             = suc n
ackPat (suc m) 0       = ackPat m 1
ackPat (suc m) (suc n) = ackPat m (ackPat (suc m) n)

ack1Rec : ℕ → ℕ → ℕ
ack1Rec 0       = recℕ ℕ 1 (λ n _ → suc n)
ack1Rec (suc m) = recℕ ℕ {!!} {!!}

ack : ℕ → ℕ → ℕ
ack = {!!}

-- add₂ : ℕ → ℕ → ℕ
-- add₂ = recℕ (ℕ → ℕ)
--             (recℕ ℕ 0 (λ n _ → suc n))
--             (λ m _ → recℕ ℕ (suc m) (λ _ ans → suc ans))

-- Ex1.11 ¬ (¬ (¬ A)) → ¬ A
prop₀ : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
prop₀ ¬¬¬a a = ¬¬¬a (λ ¬a → ¬a a)

-- Ex1.12

-- (i) A → (B → A)
prop₁ : {A B : Set} → A → B → A
prop₁ = λ a b → a

-- (ii) A → ¬ (¬ A)
prop₂ : {A : Set} → A → ¬ (¬ A)
prop₂ = λ a ¬a → ¬a a

-- (iii) (¬ A + ¬ B) → ¬ (A × B)
prop₃ : {A B : Set} → (¬ A + ¬ B) → ¬ (A × B)
prop₃ = rec+ (λ ¬a a×b → ¬a (proj₁ a×b))
             (λ ¬b a×b → ¬b (proj₂ a×b))

-- Ex1.13 ¬ (¬ (P + ¬ P))
prop₄ : {P : Set} → ¬ (¬ (P + ¬ P))
prop₄ ¬[pv¬p] = ¬[pv¬p] (inr (λ p → ¬[pv¬p] (inl p)))

-- Ex1.14

-- Ex1.15
indiscernability : {A : Set} (C : A → Set) →
                   (x y : A) → (p : x ≡ y) → C x → C y
indiscernability C x .x (refl .x) = λ x → x

indiscernability' : {A : Set} (C : A → Set) →
                    (x y : A) → (p : x ≡ y) → C x → C y
indiscernability' = {!!}


-- Ex1.16
add-right-unit : (i : ℕ) → add i 0 ≡ i
add-right-unit = indℕ (λ i → add i 0 ≡ i)
                      (refl 0)
                      (λ i i+0≡i → cong suc i+0≡i)

add-left-unit : (i : ℕ) → add 0 i ≡ i
add-left-unit = indℕ (λ i → add 0 i ≡ i)
                     (refl 0)
                     (λ i 0+i≡i → cong suc 0+i≡i)

add-suc : (i j : ℕ) → add (suc i) j ≡ add i (suc j)
add-suc = indℕ (λ i → (j : ℕ) → (add (suc i) j ≡ add i (suc j)))
               (λ j → add-left-unit (suc j))
               (λ i si+j≡i+sj j → cong suc (si+j≡i+sj j))


add-comm : (i j : ℕ) → add i j ≡ add j i
add-comm = indℕ (λ i → (j : ℕ) → add i j ≡ add j i)
                (λ j → sym (add-right-unit j))
                (λ i i+j≡j+i j → trans (cong suc (i+j≡j+i j)) (add-suc j i))
