{-# OPTIONS --without-K #-}

module Circle where

open import HoTT
open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function

-- Proof:

module Circle1 where
  private 
    data S¹* : Set where
      base* : S¹*

  S¹ : Set
  S¹ = S¹*

  base : S¹
  base = base*

  postulate 
    loop : base ≡ base

  recS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → S¹ → C
  recS¹ cbase cloop base* = cbase

  postulate
    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (recS¹ cbase cloop) loop ≡ cloop
 
  indS¹ : {C : S¹ → Set} → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
    (circle : S¹) → C circle
  indS¹ cbase cloop base* = cbase

  postulate
    βindS¹ : {C : S¹ → Set} → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (indS¹ {C} cbase cloop) loop ≡ cloop

open Circle1 public

module Circle2 where
  private 
    data S¹'* : Set where
      south* : S¹'*
      north* : S¹'*

  S¹' : Set
  S¹' = S¹'*

  south : S¹'
  south = south*

  north : S¹'
  north = north*

  postulate 
    east : south ≡ north
    west : south ≡ north

  recS¹' : {C : Set} → 
    (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → S¹' → C
  recS¹' csouth cnorth ceast cwest south* = csouth
  recS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βreceastS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) east ≡ ceast
    βrecwestS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) west ≡ cwest
 
  indS¹' : {C : S¹' → Set} → 
    (csouth : C south) → (cnorth : C north) → 
    (ceast : transport C east csouth ≡ cnorth) → 
    (cwest : transport C west csouth ≡ cnorth) → 
    (circle : S¹') → C circle
  indS¹' csouth cnorth ceast cwest south* = csouth
  indS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βindeastS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) east ≡ ceast
    βindwestS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) west ≡ cwest

open Circle2 public

-- take base to north,
-- take loop around the entire S¹' circle
f : S¹ → S¹'
f = recS¹ north (! east · west)

-- take north, south to base
-- take west to loop, take east to refl
g : S¹' → S¹
g = recS¹' base base (refl base) loop

-- theorem 2-11-3 
2-11-3 : {A B : Set} (f g : A → B) {a a' : A} (p : a ≡ a') (q : f a ≡ g a) →
          transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) · q · (ap g p)
2-11-3 f g {a} {a'} p q =
  pathInd (λ {a a'} p → (q : f a ≡ g a) →
             transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) · q · (ap g p))
          (λ a q →
            q                               ≡⟨ unitTransR q ⟩
            q · (refl $ g a)                ≡⟨ unitTransL $ q · (refl $ g a) ⟩
            (refl $ f a) · q · (refl $ g a) ∎)
          {a} {a'} p q

-- homotopy 1 : (x : S¹) → g (f x) ≡ x
βcircle : (g ∘ f) ∼ id
βcircle = indS¹ (refl base) cloop where
  cloop = transport (λ z → (g ∘ f) z ≡ id z) loop (refl base)
          ≡⟨ 2-11-3 (g ∘ f) id loop (refl base) ⟩
          ! (ap (g ∘ f) loop) · refl base · (ap id loop)
          ≡⟨ ap (λ x → ! (ap (g ∘ f) loop) · refl base · x) (apfId loop) ⟩
          ! (ap (g ∘ f) loop) · refl base · loop
          ≡⟨ ap (λ x → ! x · refl base · loop) (! (apfComp f g loop))  ⟩
          ! (ap g (ap f loop)) · refl base · loop
          ≡⟨ ap (λ x → ! (ap g x) · refl base · loop) (βrecS¹ north (! east · west)) ⟩
          ! (ap g (! east · west)) · refl base · loop
          ≡⟨ ap (λ x → ! x · refl base · loop) (apfTrans g (! east) west) ⟩
          ! (ap g (! east) · ap g west) · refl base · loop
          ≡⟨ ap (λ x → ! (ap g (! east) · x) · refl base · loop) (βrecwestS¹' base base (refl base) loop) ⟩
          ! (ap g (! east) · loop) · refl base · loop
          ≡⟨ ap (λ x → ! (x · loop) · refl base · loop) (apfInv g east) ⟩
          ! (! (ap g east) · loop) · refl base · loop
          ≡⟨ ap (λ x → ! (! x · loop) · refl base · loop) (βreceastS¹' base base (refl base) loop) ⟩
          ! (! (refl base) · loop) · refl base · loop
          ≡⟨ ap (λ x → x · refl base · loop) (invComp (! $ refl base) loop) ⟩
          (! loop · ! (! $ refl base)) · refl base · loop
          ≡⟨ ap (λ x → (! loop · x) · refl base · loop) (invId $ refl base) ⟩
          (! loop · refl base) · refl base · loop
          ≡⟨ ap (λ x → (! loop · refl base) · x) (! $ unitTransL loop) ⟩
          (! loop · refl base) · loop
          ≡⟨ ! $ assocP (! loop) (refl base) loop ⟩
          ! loop · (refl base · loop)
          ≡⟨ ap (λ x → ! loop · x) (! $ unitTransL loop) ⟩
          ! loop · loop
          ≡⟨ invTransL loop ⟩
          refl base
          ∎

-- homotopy 2 : (x : S¹') → f (g x) ≡ x
βcircle' : (f ∘ g) ∼ id
βcircle' = indS¹' (! east) (refl north) ceast cwest where
  ceast = transport (λ z → (f ∘ g) z ≡ id z) east (! east)
          ≡⟨ 2-11-3 (f ∘ g) id east (! east) ⟩
          ! (ap (f ∘ g) east) · ! east · (ap id east)
          ≡⟨ ap (λ x → ! (ap (f ∘ g) east) · ! east · x) (apfId east) ⟩
          ! (ap (f ∘ g) east) · ! east · east
          ≡⟨ ap (λ x → ! x · ! east · east) (! (apfComp g f east)) ⟩
          ! (ap f (ap g east)) · ! east · east
          ≡⟨ ap (λ x → ! (ap f x) · ! east · east) (βreceastS¹' base base (refl base) loop) ⟩
          ! (ap f (refl base)) · ! east · east
          ≡⟨ ap (λ x → ! (ap f (refl base)) · x) (invTransL east) ⟩
          ! (ap f (refl base)) · refl north
          ≡⟨ refl (refl north) ⟩
          refl north
          ∎
  cwest = transport (λ z → (f ∘ g) z ≡ id z) west (! east)
          ≡⟨ 2-11-3 (f ∘ g) id west (! east) ⟩
          ! (ap (f ∘ g) west) · ! east · (ap id west)
          ≡⟨ ap (λ x → ! (ap (f ∘ g) west) · ! east · x) (apfId west) ⟩
          ! (ap (f ∘ g) west) · ! east · west
          ≡⟨ ap (λ x → ! x · ! east · west) (! (apfComp g f west)) ⟩
          ! (ap f (ap g west)) · ! east · west
          ≡⟨ ap (λ x → ! (ap f x) · ! east · west) (βrecwestS¹' base base (refl base) loop) ⟩
          ! (ap f loop) · ! east · west
          ≡⟨ ap (λ x → ! x · ! east · west) (βrecS¹ north (! east · west)) ⟩
          ! (! east · west) · ! east · west
          ≡⟨ ap (λ x → x · ! east · west) (invComp (! east) west) ⟩
          (! west · ! (! east)) · ! east · west
          ≡⟨ ap (λ x → (! west · x) · ! east · west) (invId east) ⟩
          (! west · east) · ! east · west
          ≡⟨ assocP (! west · east) (! east) west ⟩
          ((! west · east) · ! east) · west
          ≡⟨ ap (λ x → x · west) (! $ assocP (! west) east (! east)) ⟩
          (! west · (east · ! east)) · west
          ≡⟨ ap (λ x → (! west · x) · west) (invTransR east) ⟩
          (! west · refl south) · west
          ≡⟨ ! $ assocP (! west) (refl south) west ⟩
          ! west · (refl south · west)
          ≡⟨ ap (λ x → ! west · x) (! $ unitTransL west) ⟩
          ! west · west
          ≡⟨ invTransL west ⟩
          refl north
          ∎ 

sequiv : S¹ ≃ S¹'
sequiv = f , mkisequiv g βcircle' g βcircle

spath : S¹ ≡ S¹'
spath with univalence 
... | (_ , eq) = isequiv.g eq sequiv

------------------------------------------------------------------------------
