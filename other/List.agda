module List where

open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product
open import Data.Empty
open import Data.List

-- data List (A : Set) : Set where
--   Nil  : List A
--   _::_ : A → List A → List A

-- nLs : List ℕ
-- nLs = Nil

-- testls : List ℕ
-- testls = 1 :: (2 :: Nil)

recList : {A : Set} → (C : Set) → C → (A → List A → C → C) → List A → C
recList C c f [] = c
recList C c f (x ∷ ls) = f x ls (recList C c f ls)

indList : {A : Set} → (C : List A → Set) → C [] →
          ((x : A) → (xs : List A) → C xs → C (x ∷ xs)) →
          (xs : List A) → C xs
indList C c _ []       = c
indList C c f (a ∷ as) = f a as (indList C c f as)


-- -- a little exercise
-- appendIdLeft : {A : Set} → (xs : List A) → Nil ++ xs ≡ xs
-- appendIdLeft {A} = indList (λ xs → Nil ++ xs ≡ xs)
--                            refl
--                            (λ x xs []++xs≡xs →
--                              cong (λ ls → x :: ls) []++xs≡xs)

-- appendAssoc : {A : Set} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
-- appendAssoc {A} = indList (λ xs → (ys zs : List A) →
--                              xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs)
--                           (λ _ _ → refl)
--                           (λ x _ xs++[ys++zs]≡[xs++ys]++zs ys zs →
--                             cong (λ ls → x :: ls) (xs++[ys++zs]≡[xs++ys]++zs ys zs))

-- reverseDistsOverAppend : {A : Set} → (xs ys : List A) →
--                          reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
-- reverseDistsOverAppend {A} = indList (λ xs → (ys : List A) →
--                                         reverse (xs ++ ys) ≡ reverse ys ++ reverse xs)
--                                      (λ ys → {!!})
--                                      {!!}

-- doubleReverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
-- doubleReverse = indList (λ xs → reverse (reverse xs) ≡ xs)
--                         refl
--                         (λ x xs rev[rev[xs]]≡xs → {!!})

-- Dan
recℕ : (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ C c f 0 = c
recℕ C c f (suc n) = f n (recℕ C c f n)

-- length : {A : Set} → List A → ℕ
-- length = recList ℕ 0 (λ _ _ acc → suc acc)

data LTELS {A B : Set} : (xs : List A) → (ys : List B) → Set where
  LTENil  : {ys : List B} → LTELS [] ys
  LTECons : {xs : List A} {ys : List B} →
    (x : A) → (y : B) → LTELS xs ys → LTELS (x ∷ xs) (y ∷ ys)


anLTELS : LTELS [] (5 ∷ [])
anLTELS = LTENil

anotherLTELS : LTELS (1 ∷ []) (1 ∷ 2 ∷ [])
anotherLTELS = LTECons 1 1 LTENil
