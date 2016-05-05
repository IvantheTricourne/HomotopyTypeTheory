{-# OPTIONS --without-K #-}

module EH where

open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function

infixr 8  _○_     -- path composition
infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences

------------------------------------------------------------------------------
-- A few HoTT primitives

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

--

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_○_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_○_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y : A} → x ≡ y → {z : A} → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ○ q
infixr 2 _≡⟨_⟩_

_∎ : ∀ {ℓ} {A : Set ℓ} → (x : A) → x ≡ x
x ∎ = refl x
infixl 3 _∎


--

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ○ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ○ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ○ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ○ p)
    (λ x → refl (refl x))
    {x} {y} p 

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ○ p ≡ refl y)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ○ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ○ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ○ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ○ (q ○ r) ≡ (p ○ q) ○ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ○ (q ○ r) ≡ (p ○ q) ○ r)
    (λ x z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          (refl x) ○ (q ○ r) ≡ ((refl x) ○ q) ○ r)
        (λ x w r → 
          pathInd
            (λ {x} {w} r → 
              (refl x) ○ ((refl x) ○ r) ≡ 
              ((refl x) ○ (refl x)) ○ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ○ q) ≡ ! q ○ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ○ q) ≡ ! q ○ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ○ q) ≡ ! q ○ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q

--

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ○ q) ≡ (ap f p) ○ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q = 
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ○ q) ≡ (ap f p) ○ (ap f q))
    (λ x z q → 
      pathInd {u}
        (λ {x} {z} q → 
          ap f (refl x ○ q) ≡ (ap f (refl x)) ○ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ∘ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ∘ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

--

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) → 
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
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
  _wR_ : {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → p ○ r ≡ q ○ r
  _wR_ = λ {p q} α r →
    pathInd (λ {b} {c} r   → {p q : a ≡ b} (α : p ≡ q) → p ○ r ≡ q ○ r)
            (λ b {p} {q} α →
              p ○ (refl b) ≡⟨ ! $ unitTransR p  ⟩
              p            ≡⟨ α ⟩
              q            ≡⟨ unitTransR q ⟩
              q ○ (refl b) ∎)
            r α

  _wL_ : {r s : b ≡ c} (q : a ≡ b) (β : r ≡ s) → q ○ r ≡ q ○ s
  _wL_ = λ {r s} q β →
    pathInd (λ {a} {b} q → {r s : b ≡ c} (β : r ≡ s) → q ○ r ≡ q ○ s)
            (λ a {r} {s} β →
              (refl a) ○ r ≡⟨ ! $ unitTransL r ⟩
              r            ≡⟨ β ⟩
              s            ≡⟨ unitTransL s ⟩
              (refl a) ○ s ∎)
            q β
            
-- Horizontal Composition
module _ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} where
  _⋆_ : (α : p ≡ q) (β : r ≡ s) → p ○ r ≡ q ○ s
  -- α ⋆ β = p ○ r ≡⟨ α wR r ⟩
  --         q ○ r ≡⟨ q wL β ⟩
  --         q ○ s ∎
  α ⋆ β = (α wR r) ○ (q wL β)
  
  _⋆′_ : (α : p ≡ q) (β : r ≡ s) → p ○ r ≡ q ○ s
  -- α ⋆′ β = p ○ r ≡⟨ p wL β ⟩
  --          p ○ s ≡⟨ α wR s ⟩
  --          q ○ s ∎
  α ⋆′ β = (p wL β) ○ (α wR s)

-- gave up on this... come back later
α⋆β≡α⋆′β : {A : Set} {a : A} {p q : a ≡ a} (α : p ≡ q) {r s : a ≡ a} (β : r ≡ s) → α ⋆ β ≡ α ⋆′ β
-- α⋆β≡α⋆′β (refl ._) (refl ._) = refl _
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
                 
-- ⋆ → ○
module _ {A : Set} {a : A} where
  _⋆○_ : (α : refl a ≡ refl a) (β : refl a ≡ refl a) → α ⋆ β ≡ α ○ β
  α ⋆○ β = α ⋆ β                                                 ≡⟨ refl _ ⟩
           (α wR refl a) ○ (refl a wL β)                         ≡⟨ refl _ ⟩
           (! (unitTransR $ refl a) ○ α ○ unitTransR (refl a)) ○
           (! (unitTransL $ refl a) ○ β ○ unitTransL (refl a))   ≡⟨ refl _ ⟩
           (! (refl $ refl a) ○ α ○ (refl $ refl a)) ○
           (! (refl $ refl a) ○ β ○ (refl $ refl a))             ≡⟨ refl _ ⟩
           (! (refl $ refl a) ○ (α ○ (refl $ refl a))) ○
           (! (refl $ refl a) ○ (β ○ (refl $ refl a)))           ≡⟨ ap2 _○_ (! (unitTransL (α ○ (refl $ refl a)))) (! (unitTransL (β ○ (refl $ refl a)))) ⟩
           (α ○ (refl $ refl a)) ○ (β ○ (refl $ refl a))         ≡⟨ ap2 _○_ (! (unitTransR α)) (! (unitTransR β)) ⟩
           α ○ β                                                 ∎


  _⋆′○_ : (α : refl a ≡ refl a) (β : refl a ≡ refl a) → α ⋆′ β ≡ β ○ α
  α ⋆′○ β = α ⋆′ β                                                ≡⟨ refl _ ⟩
            (refl a) wL β ○ α wR (refl a)                         ≡⟨ refl _ ⟩
            (! (unitTransL $ refl a) ○ β ○ unitTransR (refl a)) ○
            (! (unitTransR $ refl a) ○ α ○ unitTransL (refl a))   ≡⟨ refl _ ⟩
            (! (refl $ refl a) ○ β ○ (refl $ refl a)) ○
            (! (refl $ refl a) ○ α ○ (refl $ refl a))             ≡⟨ refl _ ⟩
            (! (refl $ refl a) ○ (β ○ (refl $ refl a))) ○
            (! (refl $ refl a) ○ (α ○ (refl $ refl a)))           ≡⟨ ap2 _○_ (! (unitTransL (β ○ (refl $ (refl a))))) ((! (unitTransL (α ○ (refl $ refl a))))) ⟩
            (β ○ (refl $ refl a)) ○ (α ○ (refl $ refl a))         ≡⟨ ap2 _○_ ((! (unitTransR β))) ((! (unitTransR α))) ⟩
            β ○ α                                                 ∎

eckmann-hilton : {A : Set} {a : A} (α β : Ω² A {a}) → α ○ β ≡ β ○ α 
eckmann-hilton {A} {a} α β = α ○ β  ≡⟨ ! $ α ⋆○ β ⟩
                             α ⋆ β  ≡⟨ α⋆β≡α⋆′β α β ⟩
                             α ⋆′ β ≡⟨ α ⋆′○ β ⟩
                             β ○ α ∎
 
------------------------------------------------------------------------------
