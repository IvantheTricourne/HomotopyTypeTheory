{-# OPTIONS --without-K #-}

module T where

open import Level using (_⊔_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Function renaming (_∘_ to _○_)

import Relation.Binary.Core as C
import Relation.Binary.PropositionalEquality as P
open P.≡-Reasoning

infixr 8  _∘_     -- path composition
infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences

------------------------------------------------------------------------------
-- Some abbreviations and simple lemmas and paths

_≡_ : ∀ {ℓ} {A : Set ℓ} → (x y : A) → Set ℓ
_≡_ {ℓ} {A} x y = C._≡_ {ℓ} {A} x y

-- Groupoid 

refl : ∀ {ℓ} {A} → (x : A) → x ≡ x
refl {ℓ} {A} x = C.refl {ℓ} {A} {x}

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = P.sym

_∘_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ = P.trans      

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL C.refl = C.refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR C.refl = C.refl

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp C.refl C.refl = C.refl

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP C.refl C.refl C.refl = C.refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL C.refl = C.refl

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId C.refl = C.refl

-- Functors

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
     (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
ap = P.cong     

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId C.refl = C.refl

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv f C.refl = C.refl

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans f C.refl C.refl = C.refl

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp f g C.refl = C.refl

apconst : {A B : Set} {x y : A} → (p : x ≡ y) (b : B) →
          ap (λ _ → b) p ≡ refl b
apconst C.refl b = C.refl 

-- Transport

transport : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) →
            {x y : A} → (x ≡ y) → B x → B y
transport = P.subst

transportId : {A B : Set} {y z : A} → (f g : A → B) → 
  (p : y ≡ z) → (q : f y ≡ g y) → 
  transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ q ∘ (ap g p)
transportId f g C.refl q =
  begin (q
          ≡⟨ unitTransR q ⟩
         q ∘ C.refl
          ≡⟨ unitTransL (q ∘ C.refl) ⟩
         ! C.refl ∘ (q ∘ C.refl) ∎)

apd : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : A → Set ℓ₂} →
      (f : (x : A) → B x) → {x y : A} → (p : x ≡ y) →
      transport B p (f x) ≡ f y
apd f C.refl = C.refl

-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

iso : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
iso (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
-- Some higher-inductive types

module Circle where

  private 
    data S¹* : Set where
      base* : S¹*

  -- define the interface for S¹

  S¹ : Set
  S¹ = S¹*

  base : S¹
  base = base*

  postulate 
    loop : base ≡ base

  -- recursion principle

  recS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → S¹ → C
  recS¹ cbase cloop base* = cbase

  postulate
    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (recS¹ cbase cloop) loop ≡ cloop

  -- induction principle
 
  indS¹ : {C : S¹ → Set} → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
    (circle : S¹) → C circle
  indS¹ cbase cloop base* = cbase

------------------------------------------------------------------------------
module Suspension where

  private 
    data ∑* (A : Set) : Set where
      N* : ∑* A
      S* : ∑* A

  -- define the interface for ∑A

  ∑ : (A : Set) → Set
  ∑ = ∑*

  N : {A : Set} → ∑ A
  N = N*

  S : {A : Set} → ∑ A
  S = S*

  postulate 
    merid : {A : Set} → A → (N {A} ≡ S {A})

  -- recursion principle

  rec∑ : {A : Set} → {C : Set} → (cn cs : C) → (cm : A → (cn ≡ cs)) → ∑ A → C
  rec∑ cn cs cm N* = cn
  rec∑ cn cs cm S* = cs 

  postulate
    βrec∑ : {A : Set} → {C : Set} → (cn cs : C) → (cm : A → (cn ≡ cs)) → 
      (a : A) → ap (rec∑ cn cs cm) (merid a) ≡ (cm a)

  -- induction principle
 
  ind∑ : {A : Set} → {C : ∑ A → Set} → (cn : C N) → (cs : C S) →
         ((a : A) → transport C (merid a) cn ≡ cs) → (s : ∑ A) → C s
  ind∑ cn cs m N* = cn
  ind∑ cn cs m S* = cs 

------------------------------------------------------------------------------
module Join where

  private 
    data _**_ (A B : Set) : Set where
      inl* : A → A ** B
      inr* : B → A ** B

  -- define the interface for A*B

  _*_ : (A B : Set) → Set
  A * B = A ** B

  inl : {A B : Set} → A → A * B
  inl = inl*

  inr : {A B : Set} → B → A * B
  inr = inr*

  postulate 
    glue : {A B : Set} → (c : A × B) → inl (proj₁ c) ≡ inr (proj₂ c)

  -- recursion principle

  rec* : {A B : Set} {D : Set} →
         (ad : A → D) → (bd : B → D) →
         (gd : (c : A × B) → ad (proj₁ c) ≡ bd (proj₂ c)) → 
         A * B → D
  rec* ad bd gd (inl* a) = ad a
  rec* ad bd gd (inr* b) = bd b

  postulate
    βrec* : {A B : Set} {D : Set} →
            (ad : A → D) → (bd : B → D) →
            (gd : (c : A × B) → ad (proj₁ c) ≡ bd (proj₂ c)) → 
            (c : A × B) → ap (rec* ad bd gd) (glue c) ≡ gd c

  -- induction principle
 
  ind* : {A B : Set} {D : A * B → Set} →
         (ad : (a : A) → D (inl a)) → (bd : (b : B) → D (inr b)) →
         (gd : (c : A × B) → transport D (glue c) (ad (proj₁ c)) ≡ bd (proj₂ c))
         (c : A * B) → D c
  ind* ad bd gd (inl* a) = ad a
  ind* ad bd gd (inr* b) = bd b

------------------------------------------------------------------------------
-- Lemma 6.5.1

module ∑Bool≡S¹ where

  open Circle
  open Suspension

  east : N ≡ S
  east = merid false

  west : N ≡ S
  west = merid true

  -- S¹ → ∑ Bool

  fcircle : S¹ → ∑ Bool
  fcircle = recS¹ N (east ∘ ! west)

  floop : ap fcircle loop ≡ east ∘ ! west
  floop = βrecS¹ N (east ∘ ! west)

  -- ∑ Bool → S¹

  gcircle : ∑ Bool → S¹
  gcircle = rec∑ base base (λ b → if b then refl base else loop)

  geast : ap gcircle east ≡ loop
  geast = βrec∑ base base (λ b → if b then refl base else loop) false

  gwest : ap gcircle west ≡ (refl base)
  gwest = βrec∑ base base (λ b → if b then refl base else loop) true

  -- round trip S¹ → S¹

  gf : S¹ → S¹
  gf = gcircle ○ fcircle

  gfloop : ap gf loop ≡ loop
  gfloop =
    begin (ap gf loop
             ≡⟨ ! (apfComp fcircle gcircle loop) ⟩ 
           ap gcircle (ap fcircle loop)
             ≡⟨ ap (ap gcircle) floop ⟩
           ap gcircle (east ∘ ! west)
             ≡⟨ apfTrans gcircle east (! west) ⟩
           ap gcircle east ∘ ap gcircle (! west) 
             ≡⟨ ap (λ x → ap gcircle east ∘ x) (apfInv gcircle west) ⟩
           ap gcircle east ∘ ! (ap gcircle west)
             ≡⟨ ap (λ x → ap gcircle east ∘ ! x) gwest ⟩
           ap gcircle east ∘ (refl base)
             ≡⟨ ! (unitTransR (ap gcircle east)) ⟩ 
           ap gcircle east
             ≡⟨ geast ⟩ 
           loop ∎)

  αloop : transport (λ x → gf x ≡ x) loop (refl base) ≡ refl base
  αloop =
    begin (transport (λ x → gf x ≡ x) loop (refl base) 
            ≡⟨ transportId gf id loop (refl base) ⟩ 
          ! (ap gf loop) ∘ refl base ∘ ap id loop
            ≡⟨ ap (λ x → ! (ap gf loop) ∘ refl base ∘ x) (apfId loop) ⟩
          ! (ap gf loop) ∘ refl base ∘ loop
            ≡⟨ ap (λ x → ! (ap gf loop) ∘ x) (! (unitTransL loop)) ⟩ 
          ! (ap gf loop) ∘ loop
            ≡⟨ ap (λ x → ! x ∘ loop) gfloop ⟩ 
          ! loop ∘ loop
            ≡⟨ invTransL loop ⟩ 
          refl base ∎)
  
  βcircle : gf ∼ id
  βcircle = indS¹ {λ x → gf x ≡ x} (refl base) αloop

  -- round trip ∑ Bool → ∑ Bool

  fg : ∑ Bool → ∑ Bool
  fg = fcircle ○ gcircle

  fgeast : ap fg east ≡ east ∘ ! west
  fgeast =
    begin (ap fg east 
             ≡⟨ ! (apfComp gcircle fcircle east) ⟩
           ap fcircle (ap gcircle east)
             ≡⟨ ap (ap fcircle) geast ⟩
           ap fcircle loop
             ≡⟨ floop ⟩
           (east ∘ ! west) ∎)

  fgwest : ap fg west ≡ refl N
  fgwest =
    begin (ap fg west
             ≡⟨ ! (apfComp gcircle fcircle west) ⟩ 
           ap fcircle (ap gcircle west) 
             ≡⟨ ap (ap fcircle) gwest ⟩
           ap fcircle (refl base)
             ≡⟨ C.refl ⟩
           refl N ∎)

  αeast : transport (λ x → fg x ≡ x) east (refl N) ≡ west
  αeast =
    begin (transport (λ x → fg x ≡ x) east (refl N) 
            ≡⟨ transportId fg id east (refl N) ⟩ 
          ! (ap fg east) ∘ refl N ∘ ap id east
            ≡⟨ ap (λ x → ! (ap fg east) ∘ refl N ∘ x) (apfId east) ⟩
          ! (ap fg east) ∘ refl N ∘ east
             ≡⟨ ap (λ x → ! (ap fg east) ∘ x) (! (unitTransL east)) ⟩
          ! (ap fg east) ∘ east
             ≡⟨ ap (λ x → ! x ∘ east) fgeast ⟩
          ! (east ∘ ! west) ∘ east
            ≡⟨ ap (λ x → x ∘ east) (invComp east (! west)) ⟩
          (! (! west) ∘ ! east) ∘ east
            ≡⟨ ! (assocP (! (! west)) (! east) east) ⟩ 
          ! (! west) ∘ ! east ∘ east
            ≡⟨ ap (λ x → ! (! west) ∘ x) (invTransL east) ⟩
          ! (! west) ∘ refl S
            ≡⟨ ! (unitTransR (! (! west)))  ⟩
          ! (! west)
            ≡⟨ invId west ⟩
          west ∎)
  
  αwest : transport (λ x → fg x ≡ x) west (refl N) ≡ west
  αwest =
    begin (transport (λ x → fg x ≡ x) west (refl N) 
            ≡⟨ transportId fg id west (refl N) ⟩
          ! (ap fg west) ∘ refl N ∘ ap id west
            ≡⟨ ap (λ x → ! (ap fg west) ∘ refl N ∘ x) (apfId west) ⟩
          ! (ap fg west) ∘ refl N ∘ west
             ≡⟨ ap (λ x → ! (ap fg west) ∘ x) (! (unitTransL west)) ⟩
          ! (ap fg west) ∘ west
             ≡⟨ ap (λ x → ! x ∘ west) fgwest ⟩
          ! (refl N) ∘ west
            ≡⟨ ! (unitTransL west) ⟩
          west ∎)
  
  αcircle : fg ∼ id
  αcircle =
    ind∑ (refl N) west (λ { false → αeast; true → αwest })
  
  -- main lemmas

  equivlemma : ∑ Bool ≃ S¹
  equivlemma = (gcircle , iso (mkqinv fcircle βcircle αcircle)) 

  lemma : ∑ Bool ≡ S¹
  lemma with univalence 
  ... | (_ , eq) = isequiv.g eq equivlemma


------------------------------------------------------------------------------
-- Lemma 8.5.10

module ∑A≡Bool*A where
  open Suspension
  open Join

  lemma : {A : Set} → ∑ A ≡ Bool * A
  lemma {A} = {!!} 

------------------------------------------------------------------------------
-- Lemma 8.5.9

module JoinAssoc where
  open Join

  lemma : {A B C : Set} → (A * B) * C ≡ A * (B * C)
  lemma {A} {B} {C} = {!!} 

------------------------------------------------------------------------------
-- Thm 8.5.11

open Circle
open Suspension
open Join

S² S³ : Set
S² = ∑ S¹
S³ = ∑ S²

-- Proof of the main theorem

S¹*S¹≡S³ : S¹ * S¹ ≡ S³
S¹*S¹≡S³ = 
  begin (S¹ * S¹
          ≡⟨ P.cong (λ a → a * S¹) (! ∑Bool≡S¹.lemma) ⟩
         ∑ Bool * S¹
          ≡⟨ P.cong (λ a → a * S¹) ∑A≡Bool*A.lemma ⟩
         (Bool * Bool) * S¹
          ≡⟨ JoinAssoc.lemma ⟩
         Bool * (Bool * S¹)
          ≡⟨ P.cong (λ b → Bool * b) (! ∑A≡Bool*A.lemma) ⟩ 
         Bool * S²
          ≡⟨ ! ∑A≡Bool*A.lemma ⟩ 
         S³ ∎)

------------------------------------------------------------------------------
