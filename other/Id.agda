module Id where

open import Data.Nat
open import Function using (id)

{---- 

Identity Type "Propositional Equality" 

* Agda's Definitional Equality is `=`
* `refl` is reflexivity
* "the constant path (loop) at point `x`"

----}
data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

rec≡ : {A : Set} → (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl y) = reflR {y}

-- called "indiscernability of radicals"
rec≡S : {A : Set} {C : A → Set} →
        ({x y : A} (p : x ≡ y) → C x → C y)
rec≡S {C = C} p = rec≡ (λ a b → C a → C b) {id} p
                       

subst : {A : Set} {C : A → Set} → ({x y : A} → x ≡ y → C x → C y)
subst {x = x} {y = .x} (refl .x) = id
