{-# OPTIONS --safe --cubical --lossy-unification #-}
module James where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence
import ShiftAlgebra as Shift

private
  variable
    ℓ ℓ' : Level


module _
  ((X , x₀) : Pointed ℓ) where


  data James : Type ℓ where
    []   : James
    _∷_  : X → James → James
    unit : (xs : James) → xs ≡ x₀ ∷ xs


  data Word : ℕ → Type ℓ where
    shift : {n : ℕ} → Word n → Word (suc n)

    []   : Word 0
    _∷_  : {n : ℕ} → X → Word n → Word (suc n)
    unit : {n : ℕ} (w : Word n) → shift w ≡ x₀ ∷ w

    comm-∷ : {n : ℕ} (x : X) (w : Word n) → shift (x ∷ w) ≡ x ∷ (shift w)
    comm-unit : {n : ℕ} (w : Word n) →
      Square refl (comm-∷ x₀ w) (cong shift (unit w)) (unit (shift w))

  open Sequence

  Word∙ : Sequence ℓ
  Word∙ .obj = Word
  Word∙ .map = shift

  Word∞ = SeqColim Word∙

  open Coh Word∙


  []∞ : Word∞
  []∞ = incl []

  pushCoh-∷ : {n : ℕ} (x : X) (w : Word n) (𝓲 𝓳 : I) → Word∞
  pushCoh-∷ x w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (x ∷ w)
      ; (𝓲 = i1) → incl (comm-∷ x w 𝓳) })
      (inS (push (x ∷ w) 𝓲))

  _∷∞_ : X → Word∞ → Word∞
  x ∷∞ (incl w)   = incl (x ∷ w)
  x ∷∞ (push w 𝓲) = pushCoh-∷ x w 𝓲 i1

  pushCoh-unit : {n : ℕ} (w : Word n) (i : I) (𝓲 𝓳 : I) → Word∞
  pushCoh-unit w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-shift w 𝓲 𝓳
   -- ; (i = i1) → pushCoh-∷ x₀ w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (unit w i)
      ; (𝓲 = i1) → incl (comm-unit w i 𝓳) })
      (inS (push (unit w i) 𝓲))

  unit∞ : (w : Word∞) → shift∞ w ≡ x₀ ∷∞ w
  unit∞ (incl w)   i = incl (unit w i)
  unit∞ (push w 𝓲) i = pushCoh-unit w i 𝓲 i1


  module ThickElim
    (P : Word∞ → Type ℓ')
    (shiftP : (w : Word∞) → P w → P (shift∞ w))
    (pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p))
    ([]P : P []∞)
    (_∷P_ : (x : X) {w : Word∞} → P w → P (x ∷∞ w))
    (unitP : (w : Word∞) (p : P w) → PathP (λ i → P (unit∞ w i)) (shiftP _ p) (x₀ ∷P p))
    where

    open CohP P shiftP pushP


    pushCohP-∷ : {n : ℕ} (x : X) (w : Word n) (p : P (incl w))
      (𝓲 𝓳 : I) → P (pushCoh-∷ x w 𝓲 𝓳)
    pushCohP-∷ x w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-∷ x w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (x ∷P p) 𝓲
        ; (𝓳 = i1) → x ∷P (pushP _ p 𝓲) })
        (inS (x ∷P p)) 𝓲

    pushCohP-unit : {n : ℕ} (w : Word n) (p : P (incl w))
      (i : I) (𝓲 𝓳 : I) → P (pushCoh-unit w i 𝓲 𝓳)
    pushCohP-unit w p i 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-unit w i 𝓲 𝓳)) (λ 𝓲 → λ
        { (i = i0) → pushCohP-shift _ p 𝓲 𝓳
     -- ; (i = i1) → pushCohP-∷ x₀ _ p 𝓲 𝓳
        -------------
        ; (𝓳 = i0) → pushP _ (unitP _ p i) 𝓲
        ; (𝓳 = i1) → unitP _ (pushP _ p 𝓲) i })
        (inS (unitP _ p i)) 𝓲

    elim₀ : {n : ℕ} (w : Word n) → P (incl w)
    elim₀ (shift w)  = shiftP _ (elim₀ w)
    elim₀  []        = []P
    elim₀ (x ∷ w)    = x ∷P (elim₀ w)
    elim₀ (unit w i) = unitP _ (elim₀ w) i
    elim₀ (comm-∷ x w 𝓳)    = pushCohP-∷ x w (elim₀ w) i1 𝓳
    elim₀ (comm-unit w i 𝓳) = pushCohP-unit  w (elim₀ w) i i1 𝓳

    elim : (w : Word∞) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲


    elimβ-shift : (w : Word∞) → elim (shift∞ w) ≡ shiftP _ (elim w)
    elimβ-shift (incl w) = refl
    elimβ-shift (push w 𝓲) j = pushCohP-shift _ (elim₀ w) 𝓲 j

    elimβ-coh₀ : {m n : ℕ} (w : Word n) (x : Shift.Word m)
      → elim (solve w (incl x)) ≡ solveP w (elim₀ w) (Shift.elim (incl x))
    elimβ-coh₀ w (Shift.base) = refl
    elimβ-coh₀ w (Shift.shift x) i = shiftP _ (elimβ-coh₀ w x i)

    elimβ-coh : {n : ℕ} (w : Word n) (x : Shift.Word∞)
      → elim (solve w x) ≡ solveP w (elim₀ w) (Shift.elim x)
    elimβ-coh w (incl x) = elimβ-coh₀ w x
    elimβ-coh w (push x i) j = pushP _ (elimβ-coh₀ w x j) i

    elimβ-push : (w : Word∞)
      → SquareP (λ i j → P (push∞ w j))
          (cong elim (push∞ w)) (pushP _ (elim w)) refl (elimβ-shift w)
    elimβ-push (incl w) = refl
    elimβ-push (push w i) j k =
      hcomp (λ l → λ
        { (i = i0) → cube i j k
        ; (i = i1) → cube i j k
        ; (j = i0) → elimβ-coh w (Shift.push∞ (push Shift.base k) i) (~ l)
        ; (j = i1) → cube i j k
        ; (k = i0) → cube i j k
        ; (k = i1) → cube i j k })
        (cube i j k)
        where
        cube : (i j k : I) → P (push∞ (push w i) k)
        cube i j k = solveP w (elim₀ w) (Shift.elim-push-cube i j k)


    elimβ-∷ : (x : X) (w : Word∞) → elim (x ∷∞ w) ≡ x ∷P (elim w)
    elimβ-∷ x (incl w)     = refl
    elimβ-∷ x (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-∷ x w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (x ∷ w)
        ; (𝓲 = i1) → elim₀ (comm-∷ x w 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-∷ x w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-∷ x w (elim₀ w) 𝓲 𝓳 })
        (elim (push (x ∷ w) 𝓲))

    elimβ-unit : (w : Word∞)
      → SquareP (λ i _ → P (unit∞ w i))
          (elimβ-shift w) (elimβ-∷ x₀ w) (cong elim (unit∞ w)) (unitP _ (elim w))
    elimβ-unit (incl w)   _ = refl
    elimβ-unit (push w 𝓲) i 𝓴 =
      comp (λ 𝓳 → P (pushCoh-unit w i 𝓲 𝓳)) (λ 𝓳 → λ
        { (i = i0) → pushCohP-shift w (elim₀ w) 𝓲 (𝓳 ∧ 𝓴)
     -- ; (i = i1) → elimβ-∷-cube x₀ w 𝓲 𝓳 𝓴
        -------------
        ; (𝓲 = i0) → elim₀ (unit w i)
        ; (𝓲 = i1) → elim₀ (comm-unit w i 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-unit w i 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-unit w (elim₀ w) i 𝓲 𝓳 })
       (elim (push (unit w i) 𝓲))


  normCoh-unit : (w : Word∞) (i : I) (𝓲 : I) → Word∞
  normCoh-unit w i 𝓲 = compPath-filler' (push∞ w) (unit∞ w) 𝓲 i

  norm-unit∞ : (w : Word∞) → w ≡ x₀ ∷∞ w
  norm-unit∞ w i = normCoh-unit w i i1

  module ThinElim
    (P : Word∞ → Type ℓ')
    ([]P : P []∞)
    (_∷P_ : (x : X) {w : Word∞} → P w → P (x ∷∞ w))
    (norm-unitP : (w : Word∞) (p : P w) → PathP (λ i → P (norm-unit∞ w i)) p (x₀ ∷P p))
    where

    transport-push∞ : (w : Word∞) (p : P w) (i : I) → P (push∞ w i)
    transport-push∞ w p i = transport-filler (λ i → P (push∞ w i)) p i

    shiftP : (w : Word∞) → P w → P (shift∞ w)
    shiftP w p = transport-push∞ w p i1

    pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p)
    pushP w p i = transport-push∞ w p i

    normCohP-unit : (w : Word∞) (p : P w) (i : I) (𝓲 : I) → P (normCoh-unit w i 𝓲)
    normCohP-unit w p i 𝓲 =
      fill (λ 𝓲 → P (normCoh-unit w i (~ 𝓲))) (λ 𝓲 → λ
        { (i = i0) → pushP w p 𝓲
        ; (i = i1) → x₀ ∷P p })
        (inS (norm-unitP w p i)) (~ 𝓲)

    unitP : (w : Word∞) (p : P w) → PathP (λ i → P (unit∞ w i)) (shiftP _ p) (x₀ ∷P p)
    unitP w p i = normCohP-unit w p i i0

    module Thick = ThickElim P shiftP pushP []P _∷P_ unitP

    elim : (w : Word∞) → P w
    elim = Thick.elim

    elimβ-[] : elim []∞ ≡ []P
    elimβ-[] = refl

    elimβ-∷ : (x : X) (w : Word∞) → elim (x ∷∞ w) ≡ x ∷P (elim w)
    elimβ-∷ = Thick.elimβ-∷

    elimβ-unit : (w : Word∞)
      → SquareP (λ i _ → P (norm-unit∞ w i))
          refl (elimβ-∷ x₀ w) (cong elim (norm-unit∞ w)) (norm-unitP _ (elim w))
    elimβ-unit w i 𝓳 =
      comp (λ 𝓲 → P (normCoh-unit w i 𝓲)) (λ 𝓲 → λ
        { (i = i0) → Thick.elimβ-push w 𝓳 (~ 𝓲)
        ; (i = i1) → elimβ-∷ x₀ w 𝓳
        -------------
        ; (𝓳 = i0) → elim (normCoh-unit w i 𝓲)
        ; (𝓳 = i1) → normCohP-unit w (elim w) i 𝓲 })
        (Thick.elimβ-unit w i 𝓳)
