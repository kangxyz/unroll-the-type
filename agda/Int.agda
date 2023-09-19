{-# OPTIONS --safe --cubical --lossy-unification #-}
module Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence
import ShiftAlgebra as Shift


private
  variable
    ℓ : Level


data Int : Type where
  base : Int
  cons : Int → Int
  linv : Int → Int
  rinv : Int → Int
  leq  : (x : Int) → linv (cons x) ≡ x
  req  : (x : Int) → cons (rinv x) ≡ x


data Word : ℕ → Type where
  shift : {n : ℕ} → Word n → Word (suc n)
  base  : Word 0
  cons  : {n : ℕ} → Word n → Word (suc n)
  linv  : {n : ℕ} → Word n → Word (suc n)
  rinv  : {n : ℕ} → Word n → Word (suc n)
  leq   : {n : ℕ} (w : Word n) → linv (cons w) ≡ shift (shift w)
  req   : {n : ℕ} (w : Word n) → cons (rinv w) ≡ shift (shift w)
  comm-cons : {n : ℕ} (w : Word n) → shift (cons w) ≡ cons (shift w)
  comm-linv : {n : ℕ} (w : Word n) → shift (linv w) ≡ linv (shift w)
  comm-rinv : {n : ℕ} (w : Word n) → shift (rinv w) ≡ rinv (shift w)
  comm-leq  : {n : ℕ} (w : Word n) →
    Square (comm-linv (cons w) ∙ (λ i → linv (comm-cons w i)))
      refl (cong shift (leq w)) (leq (shift w))
  comm-req  : {n : ℕ} (w : Word n) →
    Square (comm-cons (rinv w) ∙ (λ i → cons (comm-rinv w i)))
      refl (cong shift (req w)) (req (shift w))

open Sequence

Word∙ : Sequence ℓ-zero
Word∙ .obj = Word
Word∙ .map = shift

Word∞ = SeqColim Word∙

open Coh Word∙


base∞ : Word∞
base∞ = incl base


pushCoh-cons : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word∞
pushCoh-cons w 𝓲 =
  hfill (λ 𝓳 → λ
    { (𝓲 = i0) → incl (cons w)
    ; (𝓲 = i1) → incl (comm-cons w 𝓳) })
    (inS (push (cons w) 𝓲))

cons∞ : Word∞ → Word∞
cons∞ (incl w)   = incl (cons w)
cons∞ (push w 𝓲) = pushCoh-cons w 𝓲 i1


pushCoh-linv : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word∞
pushCoh-linv w 𝓲 =
  hfill (λ 𝓳 → λ
    { (𝓲 = i0) → incl (linv w)
    ; (𝓲 = i1) → incl (comm-linv w 𝓳) })
    (inS (push (linv w) 𝓲))

pushCoh-rinv : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word∞
pushCoh-rinv w 𝓲 =
  hfill (λ 𝓳 → λ
    { (𝓲 = i0) → incl (rinv w)
    ; (𝓲 = i1) → incl (comm-rinv w 𝓳) })
    (inS (push (rinv w) 𝓲))


linv∞ : Word∞ → Word∞
linv∞ (incl w)   = incl (linv w)
linv∞ (push w 𝓲) = pushCoh-linv w 𝓲 i1

rinv∞ : Word∞ → Word∞
rinv∞ (incl w)   = incl (rinv w)
rinv∞ (push w 𝓲) = pushCoh-rinv w 𝓲 i1


comm-linv-cons-filler : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word (3 + n)
comm-linv-cons-filler w 𝓲 =
  hfill (λ 𝓳 → λ
    { (𝓲 = i0) → shift (linv (cons w))
    ; (𝓲 = i1) → linv (comm-cons w 𝓳) })
    (inS (comm-linv (cons w) 𝓲))

comm-linv-cons : {n : ℕ} (w : Word n) → shift (linv (cons w)) ≡ linv (cons (shift w))
comm-linv-cons w 𝓲 = comm-linv-cons-filler w 𝓲 i1

pushCoh-linv-cons-filler : {n : ℕ} (w : Word n) (𝓲 𝓳 𝓴 : I) → Word∞
pushCoh-linv-cons-filler w 𝓲 𝓳 =
  fill (λ _ → Word∞) (λ 𝓴 → λ
    { (𝓲 = i0) → incl (linv (cons w))
    ; (𝓲 = i1) → incl (comm-linv-cons-filler w 𝓳 𝓴)
    ; (𝓳 = i0) → push (linv (cons w)) 𝓲
    ; (𝓳 = i1) → linv∞ (pushCoh-cons w 𝓲 𝓴) })
    (inS (pushCoh-linv (cons w) 𝓲 𝓳))

pushCoh-linv-cons : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word∞
pushCoh-linv-cons w 𝓲 𝓳 = pushCoh-linv-cons-filler w 𝓲 𝓳 i1


comm-cons-rinv-filler : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word (3 + n)
comm-cons-rinv-filler w 𝓲 =
  hfill (λ 𝓳 → λ
    { (𝓲 = i0) → shift (cons (rinv w))
    ; (𝓲 = i1) → cons (comm-rinv w 𝓳) })
    (inS (comm-cons (rinv w) 𝓲))

comm-cons-rinv : {n : ℕ} (w : Word n) → shift (cons (rinv w)) ≡ cons (rinv (shift w))
comm-cons-rinv w 𝓲 = comm-cons-rinv-filler w 𝓲 i1

pushCoh-cons-rinv-filler : {n : ℕ} (w : Word n) (𝓲 𝓳 𝓴 : I) → Word∞
pushCoh-cons-rinv-filler w 𝓲 𝓳 =
  fill (λ _ → Word∞) (λ 𝓴 → λ
    { (𝓲 = i0) → incl (cons (rinv w))
    ; (𝓲 = i1) → incl (comm-cons-rinv-filler w 𝓳 𝓴)
    ; (𝓳 = i0) → push (cons (rinv w)) 𝓲
    ; (𝓳 = i1) → cons∞ (pushCoh-rinv w 𝓲 𝓴) })
    (inS (pushCoh-cons (rinv w) 𝓲 𝓳))

pushCoh-cons-rinv : {n : ℕ} (w : Word n) (𝓲 𝓳 : I) → Word∞
pushCoh-cons-rinv w 𝓲 𝓳 = pushCoh-cons-rinv-filler w 𝓲 𝓳 i1


pushCoh-leq : {n : ℕ} (w : Word n) (i : I) (𝓲 𝓳 : I) → Word∞
pushCoh-leq w i 𝓲 =
  hfill (λ 𝓳 → λ
    { (i = i0) → pushCoh-linv-cons w 𝓲 𝓳
    ; (i = i1) → push (shift (shift w)) 𝓲 -- pushCoh-shift-shift w 𝓲 𝓳
    -------------
    ; (𝓲 = i0) → incl (leq w i)
    ; (𝓲 = i1) → incl (comm-leq w i 𝓳) })
    (inS (push (leq w i) 𝓲))

pushCoh-req : {n : ℕ} (w : Word n) (i : I) (𝓲 𝓳 : I) → Word∞
pushCoh-req w i 𝓲 =
  hfill (λ 𝓳 → λ
    { (i = i0) → pushCoh-cons-rinv w 𝓲 𝓳
    ; (i = i1) → push (shift (shift w)) 𝓲 -- pushCoh-shift-shift w 𝓲 𝓳
    -------------
    ; (𝓲 = i0) → incl (req w i)
    ; (𝓲 = i1) → incl (comm-req w i 𝓳) })
    (inS (push (req w i) 𝓲))


leq∞ : (w : Word∞) → linv∞ (cons∞ w) ≡ shift∞ (shift∞ w)
leq∞ (incl w)   i = incl (leq w i)
leq∞ (push w 𝓲) i = pushCoh-leq w i 𝓲 i1

req∞ : (w : Word∞) → cons∞ (rinv∞ w) ≡ shift∞ (shift∞ w)
req∞ (incl w)   i = incl (req w i)
req∞ (push w 𝓲) i = pushCoh-req w i 𝓲 i1


module ThickElim
  (P : Word∞ → Type ℓ)
  (shiftP : (w : Word∞) → P w → P (shift∞ w))
  (pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p))
  (baseP : P base∞)
  (consP : (w : Word∞) → P w → P (cons∞ w))
  (linvP : (w : Word∞) → P w → P (linv∞ w))
  (rinvP : (w : Word∞) → P w → P (rinv∞ w))
  (leqP  : (w : Word∞) (p : P w)
    → PathP (λ i → P (leq∞ w i)) (linvP _ (consP _ p)) (shiftP _ (shiftP _ p)))
  (reqP  : (w : Word∞) (p : P w)
    → PathP (λ i → P (req∞ w i)) (consP _ (rinvP _ p)) (shiftP _ (shiftP _ p)))
  where

  open CohP P shiftP pushP


  pushCohP-cons : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-cons w 𝓲 𝓳)
  pushCohP-cons w p 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-cons w 𝓲 𝓳)) (λ 𝓲 → λ
      { (𝓳 = i0) → pushP _ (consP _ p) 𝓲
      ; (𝓳 = i1) → consP _ (pushP _ p 𝓲) })
      (inS (consP _ p)) 𝓲


  pushCohP-linv : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-linv w 𝓲 𝓳)
  pushCohP-linv w p 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-linv w 𝓲 𝓳)) (λ 𝓲 → λ
      { (𝓳 = i0) → pushP _ (linvP _ p) 𝓲
      ; (𝓳 = i1) → linvP _ (pushP _ p 𝓲) })
      (inS (linvP _ p)) 𝓲

  pushCohP-rinv : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-rinv w 𝓲 𝓳)
  pushCohP-rinv w p 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-rinv w 𝓲 𝓳)) (λ 𝓲 → λ
      { (𝓳 = i0) → pushP _ (rinvP _ p) 𝓲
      ; (𝓳 = i1) → rinvP _ (pushP _ p 𝓲) })
      (inS (rinvP _ p)) 𝓲

  pushCohP-linv-cons : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-linv-cons w 𝓲 𝓳)
  pushCohP-linv-cons w p 𝓲 𝓳 =
    comp (λ 𝓴 → P (pushCoh-linv-cons-filler w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
      { (𝓲 = i0) → linvP _ (consP _ p)
   -- ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
      ; (𝓳 = i0) → pushP _ (linvP _ (consP _ p)) 𝓲
      ; (𝓳 = i1) → linvP _ (pushCohP-cons w p 𝓲 𝓴) })
      (pushCohP-linv _ (consP _ p) 𝓲 𝓳)

  pushCohP-cons-rinv : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-cons-rinv w 𝓲 𝓳)
  pushCohP-cons-rinv w p 𝓲 𝓳 =
    comp (λ 𝓴 → P (pushCoh-cons-rinv-filler w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
      { (𝓲 = i0) → consP _ (rinvP _ p)
   -- ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
      ; (𝓳 = i0) → pushP _ (consP _ (rinvP _ p)) 𝓲
      ; (𝓳 = i1) → consP _ (pushCohP-rinv w p 𝓲 𝓴) })
      (pushCohP-cons _ (rinvP _ p) 𝓲 𝓳)

  pushCohP-leq : {n : ℕ} (w : Word n) (p : P (incl w))
    (i : I) (𝓲 𝓳 : I) → P (pushCoh-leq w i 𝓲 𝓳)
  pushCohP-leq w p i 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-leq w i 𝓲 𝓳)) (λ 𝓲 → λ
      { (i = i0) → pushCohP-linv-cons   _ p 𝓲 𝓳
      ; (i = i1) → pushCohP-shift-shift _ p 𝓲 𝓳
      -------------
      ; (𝓳 = i0) → pushP _ (leqP _ p i) 𝓲
      ; (𝓳 = i1) → leqP _ (pushP _ p 𝓲) i })
      (inS (leqP _ p i)) 𝓲

  pushCohP-req : {n : ℕ} (w : Word n) (p : P (incl w))
    (i : I) (𝓲 𝓳 : I) → P (pushCoh-req w i 𝓲 𝓳)
  pushCohP-req w p i 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-req w i 𝓲 𝓳)) (λ 𝓲 → λ
      { (i = i0) → pushCohP-cons-rinv  _ p 𝓲 𝓳
      ; (i = i1) → pushCohP-shift-shift _ p 𝓲 𝓳
      -------------
      ; (𝓳 = i0) → pushP _ (reqP _ p i) 𝓲
      ; (𝓳 = i1) → reqP _ (pushP _ p 𝓲) i })
      (inS (reqP _ p i)) 𝓲


  elim₀ : {n : ℕ} (w : Word n) → P (incl w)
  elim₀ (shift w) = shiftP _ (elim₀ w)
  elim₀  base     = baseP
  elim₀ (cons w)  = consP _ (elim₀ w)
  elim₀ (linv w)  = linvP _ (elim₀ w)
  elim₀ (rinv w)  = rinvP _ (elim₀ w)
  elim₀ (leq w i) = leqP  _ (elim₀ w) i
  elim₀ (req w i) = reqP  _ (elim₀ w) i
  elim₀ (comm-cons w 𝓳)   = pushCohP-cons w (elim₀ w) i1 𝓳
  elim₀ (comm-linv w 𝓳)   = pushCohP-linv w (elim₀ w) i1 𝓳
  elim₀ (comm-rinv w 𝓳)   = pushCohP-rinv w (elim₀ w) i1 𝓳
  elim₀ (comm-leq  w i 𝓳) = pushCohP-leq  w (elim₀ w) i i1 𝓳
  elim₀ (comm-req  w i 𝓳) = pushCohP-req  w (elim₀ w) i i1 𝓳

  elim : (w : Word∞) → P w
  elim (incl w)   = elim₀ w
  elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲


  elimβ-shift : (w : Word∞) → elim (shift∞ w) ≡ shiftP _ (elim w)
  elimβ-shift (incl w) = refl
  elimβ-shift (push w 𝓲) j = pushCohP-shift _ (elim₀ w) 𝓲 j

  elimβ-shift-shift : (w : Word∞) → elim (shift∞ (shift∞ w)) ≡ shiftP _ (shiftP _ (elim w))
  elimβ-shift-shift (incl w) = refl
  elimβ-shift-shift (push w 𝓲) j = pushCohP-shift-shift _ (elim₀ w) 𝓲 j

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

{-
  elimβ-push-push₀ : {n : ℕ} (w : Word n)
    → SquareP (λ i j → P (push²∞ (incl w) j))
        (cong elim (push²∞ (incl w))) (push²P _ (elim (incl w))) refl (elimβ-shift-shift (incl w))
  elimβ-push-push₀ w = refl
-}

{-
  elimβ-push-push : (w : Word∞)
    → SquareP (λ i j → P (push²∞ w j))
        (cong elim (push²∞ w)) (push²P _ (elim w)) refl (elimβ-shift-shift w)
  elimβ-push-push = {!!}
  --elimβ-push-push (incl w) = refl
  --elimβ-push-push (push w i) = {!!}
-}

{-
  elimβ-push' : (w : Word∞)
    → SquareP (λ i j → P (push∞ w j))
        (cong elim (push∞ w)) (pushP _ (elim w)) refl (elimβ-shift w)
  elimβ-push' (incl w) = refl
  elimβ-push' (push w i) j k =
    comp (λ 𝓳 → P (pushCoh-leq w i 𝓲 𝓳)) (λ 𝓳 → λ
   -- { (i = i0) → elimβ-linv-cons-cube w 𝓲 𝓳 𝓴
      { (i = i1) → pushCohP-shift-shift _ (elim₀ w) 𝓲 (𝓳 ∧ 𝓴)
      -------------
      ; (𝓲 = i0) → elim₀ (leq w i)
      ; (𝓲 = i1) → elim₀ (comm-leq w i 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-leq w i 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-leq w (elim₀ w) i 𝓲 𝓳 })
      (elim (push (leq w i) 𝓲))
-}

  elimβ-cons : (w : Word∞) → elim (cons∞ w) ≡ consP _ (elim w)
  elimβ-cons (incl w)     = refl
  elimβ-cons (push w 𝓲) 𝓴 =
    comp (λ 𝓳 → P (pushCoh-cons w 𝓲 𝓳)) (λ 𝓳 → λ
      { (𝓲 = i0) → elim₀ (cons w)
      ; (𝓲 = i1) → elim₀ (comm-cons w 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-cons w 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-cons w (elim₀ w) 𝓲 𝓳 })
      (elim (push (cons w) 𝓲))

  elimβ-linv : (w : Word∞) → elim (linv∞ w) ≡ linvP _ (elim w)
  elimβ-linv (incl w)     = refl
  elimβ-linv (push w 𝓲) 𝓴 =
    comp (λ 𝓳 → P (pushCoh-linv w 𝓲 𝓳)) (λ 𝓳 → λ
      { (𝓲 = i0) → elim₀ (linv w)
      ; (𝓲 = i1) → elim₀ (comm-linv w 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-linv w 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-linv w (elim₀ w) 𝓲 𝓳 })
      (elim (push (linv w) 𝓲))

  elimβ-linv-cons : (w : Word∞) → elim (linv∞ (cons∞ w)) ≡ linvP _ (consP _ (elim w))
  elimβ-linv-cons (incl w)     = refl
  elimβ-linv-cons (push w 𝓲) 𝓴 =
    comp (λ 𝓳 → P (pushCoh-linv-cons w 𝓲 𝓳)) (λ 𝓳 → λ
      { (𝓲 = i0) → elim₀ (linv (cons w))
      ; (𝓲 = i1) → elim₀ (comm-linv-cons w 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-linv-cons w 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-linv-cons w (elim₀ w) 𝓲 𝓳 })
      (elim (push (linv (cons w)) 𝓲))

  elimβ-cons-rinv : (w : Word∞) → elim (cons∞ (rinv∞ w)) ≡ consP _ (rinvP _ (elim w))
  elimβ-cons-rinv (incl w)     = refl
  elimβ-cons-rinv (push w 𝓲) 𝓴 =
    comp (λ 𝓳 → P (pushCoh-cons-rinv w 𝓲 𝓳)) (λ 𝓳 → λ
      { (𝓲 = i0) → elim₀ (cons (rinv w))
      ; (𝓲 = i1) → elim₀ (comm-cons-rinv w 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-cons-rinv w 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-cons-rinv w (elim₀ w) 𝓲 𝓳 })
      (elim (push (cons (rinv w)) 𝓲))

  elimβ-leq : (w : Word∞)
    → SquareP (λ i _ → P (leq∞ w i))
        (elimβ-linv-cons w) (elimβ-shift-shift w) (cong elim (leq∞ w)) (leqP _ (elim w))
  elimβ-leq (incl w)   _ = refl
  elimβ-leq (push w 𝓲) i 𝓴 =
    comp (λ 𝓳 → P (pushCoh-leq w i 𝓲 𝓳)) (λ 𝓳 → λ
   -- { (i = i0) → elimβ-linv-cons-cube w 𝓲 𝓳 𝓴
      { (i = i1) → pushCohP-shift-shift _ (elim₀ w) 𝓲 (𝓳 ∧ 𝓴)
      -------------
      ; (𝓲 = i0) → elim₀ (leq w i)
      ; (𝓲 = i1) → elim₀ (comm-leq w i 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-leq w i 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-leq w (elim₀ w) i 𝓲 𝓳 })
      (elim (push (leq w i) 𝓲))

  elimβ-req : (w : Word∞)
    → SquareP (λ i _ → P (req∞ w i))
        (elimβ-cons-rinv w) (elimβ-shift-shift w) (cong elim (req∞ w)) (reqP _ (elim w))
  elimβ-req (incl w)   _ = refl
  elimβ-req (push w 𝓲) i 𝓴 =
    comp (λ 𝓳 → P (pushCoh-req w i 𝓲 𝓳)) (λ 𝓳 → λ
   -- { (i = i0) → elimβ-cons-rinv-cube w 𝓲 𝓳 𝓴
      { (i = i1) → pushCohP-shift-shift _ (elim₀ w) 𝓲 (𝓳 ∧ 𝓴)
      -------------
      ; (𝓲 = i0) → elim₀ (req w i)
      ; (𝓲 = i1) → elim₀ (comm-req w i 𝓳)
      ; (𝓴 = i0) → elim (pushCoh-req w i 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-req w (elim₀ w) i 𝓲 𝓳 })
      (elim (push (req w i) 𝓲))




{-
normCoh-leq : (w : Word∞) (i : I) (𝓲 : I) → Word∞
normCoh-leq w i 𝓲 = compPath-filler (leq∞ w) (sym (push²∞ w)) 𝓲 i

norm-leq∞ : (w : Word∞) → linv∞ (cons∞ w) ≡ w
norm-leq∞ w i = normCoh-leq w i i1

normCoh-req : (w : Word∞) (i : I) (𝓲 : I) → Word∞
normCoh-req w i 𝓲 = compPath-filler (req∞ w) (sym (push²∞ w)) 𝓲 i

norm-req∞ : (w : Word∞) → cons∞ (rinv∞ w) ≡ w
norm-req∞ w i = normCoh-req w i i1

module ThinElim
  (P : Word∞ → Type ℓ)
  (baseP : P base∞)
  (consP : (w : Word∞) → P w → P (cons∞ w))
  (linvP : (w : Word∞) → P w → P (linv∞ w))
  (rinvP : (w : Word∞) → P w → P (rinv∞ w))
  (norm-leqP  : (w : Word∞) (p : P w)
    → PathP (λ i → P (norm-leq∞ w i)) (linvP _ (consP _ p)) p)
  (norm-reqP  : (w : Word∞) (p : P w)
    → PathP (λ i → P (norm-req∞ w i)) (consP _ (rinvP _ p)) p)
  where

  transport-push∞ : (w : Word∞) (p : P w) (i : I) → P (push∞ w i)
  transport-push∞ w p i = transport-filler (λ i → P (push∞ w i)) p i

  transport-push²∞ : (w : Word∞) (p : P w) (i : I) → P (push²∞ w i)
  transport-push²∞ w p i = transport-filler (λ i → P (push²∞ w i)) p i

  shiftP : (w : Word∞) → P w → P (shift∞ w)
  shiftP w p = transport-push∞ w p i1

  pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p)
  pushP w p i = transport-push∞ w p i

  open CohP P shiftP pushP


  normCohP-leq : (w : Word∞) (p : P w) (i : I) (𝓲 : I) → P (normCoh-leq w i 𝓲)
  normCohP-leq w p i 𝓲 =
    fill (λ 𝓲 → P (normCoh-leq w i (~ 𝓲))) (λ 𝓲 → λ
      { (i = i0) → linvP _ (consP _ p)
      ; (i = i1) → push²P w p 𝓲 })
      (inS (norm-leqP w p i)) (~ 𝓲)

  normCohP-req : (w : Word∞) (p : P w) (i : I) (𝓲 : I) → P (normCoh-req w i 𝓲)
  normCohP-req w p i 𝓲 =
    fill (λ 𝓲 → P (normCoh-req w i (~ 𝓲))) (λ 𝓲 → λ
      { (i = i0) → consP _ (rinvP _ p)
      ; (i = i1) → push²P w p 𝓲 })
      (inS (norm-reqP w p i)) (~ 𝓲)

  leqP : (w : Word∞) (p : P w)
    → PathP (λ i → P (leq∞ w i)) (linvP _ (consP _ p)) (shiftP _ (shiftP _ p))
  leqP w p i = normCohP-leq w p i i0

  reqP : (w : Word∞) (p : P w)
    → PathP (λ i → P (req∞ w i)) (consP _ (rinvP _ p)) (shiftP _ (shiftP _ p))
  reqP w p i = normCohP-req w p i i0

  module Thick = ThickElim P shiftP pushP baseP consP linvP rinvP leqP reqP


  elim : (w : Word∞) → P w
  elim = Thick.elim

  elimβ-[] : elim base∞ ≡ baseP
  elimβ-[] = refl

  elimβ-cons : (w : Word∞) → elim (cons∞ w) ≡ consP _ (elim w)
  elimβ-cons = Thick.elimβ-cons

  elimβ-linv-cons : (w : Word∞) → elim (linv∞ (cons∞ w)) ≡ linvP _ (consP _ (elim w))
  elimβ-linv-cons = Thick.elimβ-linv-cons

  elimβ-cons-rinv : (w : Word∞) → elim (cons∞ (rinv∞ w)) ≡ consP _ (rinvP _ (elim w))
  elimβ-cons-rinv = Thick.elimβ-cons-rinv

  elimβ-leq : (w : Word∞)
    → SquareP (λ i _ → P (norm-leq∞ w i))
        (elimβ-linv-cons w) refl (cong elim (norm-leq∞ w)) (norm-leqP _ (elim w))
  elimβ-leq w i 𝓳 =
    comp (λ 𝓲 → P (normCoh-leq w i 𝓲)) (λ 𝓲 → λ
      { (i = i0) → elimβ-linv-cons w 𝓳
      ; (i = i1) → Thick.elimβ-push-push w 𝓳 (~ 𝓲)
      -------------
      ; (𝓳 = i0) → elim (normCoh-leq w i 𝓲)
      ; (𝓳 = i1) → normCohP-leq w (elim w) i 𝓲 })
      (Thick.elimβ-leq w i 𝓳)

  elimβ-req : (w : Word∞)
    → SquareP (λ i _ → P (norm-req∞ w i))
        (elimβ-cons-rinv w) refl (cong elim (norm-req∞ w)) (norm-reqP _ (elim w))
  elimβ-req w i 𝓳 =
    comp (λ 𝓲 → P (normCoh-req w i 𝓲)) (λ 𝓲 → λ
      { (i = i0) → elimβ-cons-rinv w 𝓳
      ; (i = i1) → Thick.elimβ-push-push w 𝓳 (~ 𝓲)
      -------------
      ; (𝓳 = i0) → elim (normCoh-req w i 𝓲)
      ; (𝓳 = i1) → normCohP-req w (elim w) i 𝓲 })
      (Thick.elimβ-req w i 𝓳)
-}