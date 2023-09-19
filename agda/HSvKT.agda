{-

The Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module HSvKT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence
import ShiftAlgebra as Shift


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module _
  (X : Type ℓ) (Y : Type ℓ')
  (R : X → Y → Type ℓ'')
  (a₀ : X ⊎ Y)
  where

  open Sequence

  data Code : X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    base : Code a₀
    glue : {x : X} {y : Y} (r : R x y) → Code (inl x) → Code (inr y)
    linv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    rinv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    leq  : {x : X} {y : Y} (r : R x y) (u : Code (inl x)) → linv r (glue r u) ≡ u
    req  : {x : X} {y : Y} (r : R x y) (v : Code (inr y)) → glue r (rinv r v) ≡ v


  data Word : ℕ → X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    shift : {n : ℕ} {a : X ⊎ Y} → Word n a → Word (suc n) a
    base  : Word 0 a₀
    glue  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inl x) → Word (suc n) (inr y)
    linv  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inr y) → Word (suc n) (inl x)
    leq   : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) → linv r (glue r w) ≡ shift (shift w)
    comm-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) → shift (glue r w) ≡ glue r (shift w)
    comm-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) → shift (linv r w) ≡ linv r (shift w)
    comm-leq  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) →
        Square
          (comm-linv r (glue r w) ∙ (λ i → linv r (comm-glue r w i))) refl
          (cong shift (leq r w)) (leq r (shift w))

  Word∙ : X ⊎ Y → Sequence (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∙ a .obj n = Word n a
  Word∙ _ .map   = shift

  Word∞ : X ⊎ Y → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∞ a = SeqColim (Word∙ a)

  open module CohR (a : X ⊎ Y) = Coh (Word∙ a)


  pushCoh-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-glue r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (glue r w)
      ; (𝓲 = i1) → incl (comm-glue r w 𝓳) })
      (inS (push (glue r w) 𝓲))


  pushCoh-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-linv r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (linv r w)
      ; (𝓲 = i1) → incl (comm-linv r w 𝓳) })
      (inS (push (linv r w) 𝓲))

  linv∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inr y) → Word∞ (inl x)
  linv∞ r (incl w)   = incl (linv r w)
  linv∞ r (push w 𝓲) = pushCoh-linv r w 𝓲 i1

  comm-linv-glue-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word (3 + n) (inl x)
  comm-linv-glue-filler r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → shift (linv r (glue r w))
      ; (𝓲 = i1) → linv r (comm-glue r w 𝓳) })
      (inS (comm-linv r (glue r w) 𝓲))

  comm-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) → shift (linv r (glue r w)) ≡ linv r (glue r (shift w))
  comm-linv-glue r w 𝓲 = comm-linv-glue-filler r w 𝓲 i1

  pushCoh-linv-glue-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 𝓴 : I) → Word∞ (inl x)
  pushCoh-linv-glue-filler r w 𝓲 𝓳 =
    hfill (λ 𝓴 → λ
      { (𝓲 = i0) → incl (linv r (glue r w))
      ; (𝓲 = i1) → incl (comm-linv-glue-filler r w 𝓳 𝓴)
      ; (𝓳 = i0) → push (linv r (glue r w)) 𝓲
      ; (𝓳 = i1) → linv∞ r (pushCoh-glue r w 𝓲 𝓴) })
      (inS (pushCoh-linv r (glue r w) 𝓲 𝓳))

  pushCoh-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-linv-glue r w 𝓲 𝓳 = pushCoh-linv-glue-filler r w 𝓲 𝓳 i1

  pushCoh-leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (i : I) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-leq r w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-linv-glue r w 𝓲 𝓳
      ; (i = i1) → push (shift (shift w)) 𝓲 -- pushCoh-shift-shift w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (leq r w i)
      ; (𝓲 = i1) → incl (comm-leq r w i 𝓳) })
      (inS (push (leq r w i) 𝓲))


  base∞ : Word∞ a₀
  base∞ = incl base

  glue∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inl x) → Word∞ (inr y)
  glue∞ r (incl w)   = incl (glue r w)
  glue∞ r (push w 𝓲) = pushCoh-glue r w 𝓲 i1

  leq∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) → linv∞ r (glue∞ r w) ≡ shift∞ _ (shift∞ _ w)
  leq∞ r (incl w)   i = incl (leq r w i)
  leq∞ r (push w 𝓲) i = pushCoh-leq r w i 𝓲 i1




  module ThickElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w))
    (pushP  : {a : X ⊎ Y} (w : Word∞ a) (p : P w)
      → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p))
    (baseP : P base∞)
    (glueP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (glue∞ r w))
    (linvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (linv∞ r w))
    (leqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (leq∞ r w i))
          (linvP r _ (glueP r _ p)) (shiftP _ (shiftP _ p)))
    where

    open module CohRP (a : X ⊎ Y) = CohP a P shiftP pushP


    pushCohP-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-glue r w 𝓲 𝓳)
    pushCohP-glue r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-glue r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (glueP r _ p) 𝓲
        ; (𝓳 = i1) → glueP r _ (pushP _ p 𝓲) })
        (inS (glueP r _ p)) 𝓲

    pushCohP-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-linv r w 𝓲 𝓳)
    pushCohP-linv r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-linv r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (linvP r _ p) 𝓲
        ; (𝓳 = i1) → linvP r _ (pushP _ p 𝓲) })
        (inS (linvP r _ p)) 𝓲

    pushCohP-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-linv-glue r w 𝓲 𝓳)
    pushCohP-linv-glue r w p 𝓲 𝓳 =
      comp (λ 𝓴 → P (pushCoh-linv-glue-filler r w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
        { (𝓲 = i0) → linvP r _ (glueP r _ p)
     -- ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
        ; (𝓳 = i0) → pushP _ (linvP r _ (glueP r _ p)) 𝓲
        ; (𝓳 = i1) → linvP r _ (pushCohP-glue r w p 𝓲 𝓴) })
        (pushCohP-linv r _ (glueP r _ p) 𝓲 𝓳)

    pushCohP-leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (i : I) (𝓲 𝓳 : I) → P (pushCoh-leq r w i 𝓲 𝓳)
    pushCohP-leq r w p i 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-leq r w i 𝓲 𝓳)) (λ 𝓲 → λ
        { (i = i0) → pushCohP-linv-glue   r _ p 𝓲 𝓳
        ; (i = i1) → pushCohP-shift-shift _ _ p 𝓲 𝓳
        -------------
        ; (𝓳 = i0) → pushP _ (leqP r _ p i) 𝓲
        ; (𝓳 = i1) → leqP r _ (pushP _ p 𝓲) i })
        (inS (leqP r _ p i)) 𝓲


    elim₀ : {a : X ⊎ Y} {n : ℕ} (w : Word n a) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀  base     = baseP
    elim₀ (glue r w)  = glueP r _ (elim₀ w)
    elim₀ (linv r w)  = linvP r _ (elim₀ w)
    elim₀ (leq r w i) = leqP  r _ (elim₀ w) i
    elim₀ (comm-glue r w 𝓳)   = pushCohP-glue r w (elim₀ w) i1 𝓳
    elim₀ (comm-linv r w 𝓳)   = pushCohP-linv r w (elim₀ w) i1 𝓳
    elim₀ (comm-leq  r w i 𝓳) = pushCohP-leq  r w (elim₀ w) i i1 𝓳

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲



    elimβ-shift : {a : X ⊎ Y} (w : Word∞ a) → elim (shift∞ _ w) ≡ shiftP _ (elim w)
    elimβ-shift (incl w) = refl
    elimβ-shift (push w 𝓲) j = pushCohP-shift _ _ (elim₀ w) 𝓲 j

    elimβ-shift-shift : {a : X ⊎ Y} (w : Word∞ a)
      → elim (shift∞ _ (shift∞ _ w)) ≡ shiftP _ (shiftP _ (elim w))
    elimβ-shift-shift (incl w) = refl
    elimβ-shift-shift (push w 𝓲) j = pushCohP-shift-shift _ _ (elim₀ w) 𝓲 j

    elimβ-coh₀ : {a : X ⊎ Y} {m n : ℕ} (w : Word n a) (x : Shift.Word m)
      → elim (solve _ w (incl x)) ≡ solveP _ w (elim₀ w) (Shift.elim (incl x))
    elimβ-coh₀ w (Shift.base) = refl
    elimβ-coh₀ w (Shift.shift x) i = shiftP _ (elimβ-coh₀ w x i)

    elimβ-coh : {a : X ⊎ Y} {n : ℕ} (w : Word n a) (x : Shift.Word∞)
      → elim (solve _ w x) ≡ solveP _ w (elim₀ w) (Shift.elim x)
    elimβ-coh w (incl x) = elimβ-coh₀ w x
    elimβ-coh w (push x i) j = pushP _ (elimβ-coh₀ w x j) i

    elimβ-push : {a : X ⊎ Y} (w : Word∞ a)
      → SquareP (λ i j → P (push∞ _ w j))
          (cong elim (push∞ _ w)) (pushP _ (elim w)) refl (elimβ-shift w)
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
        cube : (i j k : I) → P (push∞ _ (push w i) k)
        cube i j k = solveP _ w (elim₀ w) (Shift.elim-push-cube i j k)


    elimβ-glue : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (glue∞ r w) ≡ glueP r _ (elim w)
    elimβ-glue r (incl w)     = refl
    elimβ-glue r (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-glue r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (glue r w)
        ; (𝓲 = i1) → elim₀ (comm-glue r w 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-glue r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-glue r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (glue r w) 𝓲))

    elimβ-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inr y))  → elim (linv∞ r w) ≡ linvP r _ (elim w)
    elimβ-linv r (incl w)     = refl
    elimβ-linv r (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-linv r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (linv r w)
        ; (𝓲 = i1) → elim₀ (comm-linv r w 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-linv r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-linv r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (linv r w) 𝓲))

    elimβ-linv-glue : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (linv∞ r (glue∞ r w)) ≡ linvP r _ (glueP r _ (elim w))
    elimβ-linv-glue r (incl w)     = refl
    elimβ-linv-glue r (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-linv-glue r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (linv r (glue r w))
        ; (𝓲 = i1) → elim₀ (comm-linv-glue r w 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-linv-glue r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-linv-glue r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (linv r (glue r w)) 𝓲))

    elimβ-leq : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) →
        SquareP (λ j i → P (leq∞ r w j))
          (elimβ-linv-glue r w) (elimβ-shift-shift w) (cong elim (leq∞ r w)) (leqP r _ (elim w))
    elimβ-leq r (incl w)   _ = refl
    elimβ-leq r (push w 𝓲) i 𝓴 =
      comp (λ 𝓳 → P (pushCoh-leq r w i 𝓲 𝓳)) (λ 𝓳 → λ
     -- { (i = i0) → elimβ-linv-glue-cube r w 𝓲 𝓳 𝓴
        { (i = i1) → pushCohP-shift-shift _ _ (elim₀ w) 𝓲 (𝓳 ∧ 𝓴)
        -------------
        ; (𝓲 = i0) → elim₀ (leq r w i)
        ; (𝓲 = i1) → elim₀ (comm-leq r w i 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-leq r w i 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-leq r w (elim₀ w) i 𝓲 𝓳 })
        (elim (push (leq r w i) 𝓲))
