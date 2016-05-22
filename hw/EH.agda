{-# OPTIONS --without-K #-}

module EH where

open import HoTT

open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function

-- Path and loop spaces

1-Paths : (A : Set) → {a b : A} → Set
1-Paths A {a} {b} = (a ≡ b)

2-Paths : (A : Set) → {a b : A} {p q : 1-Paths A {a} {b}} → Set
2-Paths A {a} {b} {p} {q} = (p ≡ q)

Ω : (A : Set) → {a : A} → Set
Ω A {a} = 1-Paths A {a} {a}

Ω² : (A : Set) → {a : A} → Set
Ω² A {a} = 2-Paths A {a} {a} {refl a} {refl a}

-- Whiskering
module _ {A : Set} {a b c : A} where
  _wR_ : {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → p · r ≡ q · r
  _wR_ = λ {p q} α r →
    pathInd (λ {b} {c} r   → {p q : a ≡ b} (α : p ≡ q) → p · r ≡ q · r)
            (λ b {p} {q} α →
              p · (refl b) ≡⟨ ! $ unitTransR p  ⟩
              p            ≡⟨ α ⟩
              q            ≡⟨ unitTransR q ⟩
              q · (refl b) ∎)
            r α

  _wL_ : {r s : b ≡ c} (q : a ≡ b) (β : r ≡ s) → q · r ≡ q · s
  _wL_ = λ {r s} q β →
    pathInd (λ {a} {b} q → {r s : b ≡ c} (β : r ≡ s) → q · r ≡ q · s)
            (λ a {r} {s} β →
              (refl a) · r ≡⟨ ! $ unitTransL r ⟩
              r            ≡⟨ β ⟩
              s            ≡⟨ unitTransL s ⟩
              (refl a) · s ∎)
            q β
            
-- Horizontal Composition
module _ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} where
  _⋆_ : (α : p ≡ q) (β : r ≡ s) → p · r ≡ q · s
  α ⋆ β = (α wR r) · (q wL β)
  _⋆′_ : (α : p ≡ q) (β : r ≡ s) → p · r ≡ q · s
  α ⋆′ β = (p wL β) · (α wR s)


α⋆β≡α⋆′β : {A : Set} {a : A} {p q : a ≡ a} (α : p ≡ q) {r s : a ≡ a} (β : r ≡ s) → α ⋆ β ≡ α ⋆′ β
α⋆β≡α⋆′β = λ {A a} →
  pathInd (λ {p q} α → {r s : a ≡ a} (β : r ≡ s) → α ⋆ β ≡ α ⋆′ β)
          (λ p → pathInd (λ {r s} β → refl p ⋆ β ≡ refl p ⋆′ β )
                         (λ r → pathInd (λ {a} {b} p → {c : A} (r : b ≡ c) → refl p ⋆ refl r ≡ refl p ⋆′ refl r)
                                        (λ  a → pathInd (λ {a} {c} r → refl (refl a) ⋆ refl r ≡ refl (refl a) ⋆′ refl r)
                                                        (λ a → refl (refl (refl a)))
                                                        {a})
                                        {a} {a} p {a} r))


ap2 : {A : Set} {A′ : Set} {B : Set} (f : A → A′ → B) {x y : A} →
      x ≡ y → {x′ y′ : A′} → x′ ≡ y′ → f x x′ ≡ f y y′
ap2 = λ {A A′ B} f →
  pathInd (λ {x} {y} _ → {x′ y′ : A′} → x′ ≡ y′ → f x x′ ≡ f y y′)
          (λ x → pathInd (λ {x′} {y′} _ → f x x′ ≡ f x y′)
                         (λ x′ → refl $ f x x′))
                 
-- ⋆ → ·
module _ {A : Set} {a : A} where
  _⋆·_ : (α : refl a ≡ refl a) (β : refl a ≡ refl a) → α ⋆ β ≡ α · β
  α ⋆· β = α ⋆ β                                                 ≡⟨ refl _ ⟩
           (α wR refl a) · (refl a wL β)                         ≡⟨ refl _ ⟩
           (! (unitTransR $ refl a) · α · unitTransR (refl a)) ·
           (! (unitTransL $ refl a) · β · unitTransL (refl a))   ≡⟨ refl _ ⟩
           (! (refl $ refl a) · α · (refl $ refl a)) ·
           (! (refl $ refl a) · β · (refl $ refl a))             ≡⟨ refl _ ⟩
           (! (refl $ refl a) · (α · (refl $ refl a))) ·
           (! (refl $ refl a) · (β · (refl $ refl a)))           ≡⟨ ap2 _·_ (! (unitTransL (α · (refl $ refl a)))) (! (unitTransL (β · (refl $ refl a)))) ⟩
           (α · (refl $ refl a)) · (β · (refl $ refl a))         ≡⟨ ap2 _·_ (! (unitTransR α)) (! (unitTransR β)) ⟩
           α · β                                                 ∎


  _⋆′·_ : (α : refl a ≡ refl a) (β : refl a ≡ refl a) → α ⋆′ β ≡ β · α
  α ⋆′· β = α ⋆′ β                                                ≡⟨ refl _ ⟩
            (refl a) wL β · α wR (refl a)                         ≡⟨ refl _ ⟩
            (! (unitTransL $ refl a) · β · unitTransR (refl a)) ·
            (! (unitTransR $ refl a) · α · unitTransL (refl a))   ≡⟨ refl _ ⟩
            (! (refl $ refl a) · β · (refl $ refl a)) ·
            (! (refl $ refl a) · α · (refl $ refl a))             ≡⟨ refl _ ⟩
            (! (refl $ refl a) · (β · (refl $ refl a))) ·
            (! (refl $ refl a) · (α · (refl $ refl a)))           ≡⟨ ap2 _·_ (! (unitTransL (β · (refl $ (refl a))))) ((! (unitTransL (α · (refl $ refl a))))) ⟩
            (β · (refl $ refl a)) · (α · (refl $ refl a))         ≡⟨ ap2 _·_ ((! (unitTransR β))) ((! (unitTransR α))) ⟩
            β · α                                                 ∎

eckmann-hilton : {A : Set} {a : A} (α β : Ω² A {a}) → α · β ≡ β · α 
eckmann-hilton {A} {a} α β = α · β  ≡⟨ ! $ α ⋆· β ⟩
                             α ⋆ β  ≡⟨ α⋆β≡α⋆′β α β ⟩
                             α ⋆′ β ≡⟨ α ⋆′· β ⟩
                             β · α ∎
 
------------------------------------------------------------------------------
