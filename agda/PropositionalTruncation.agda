{-# OPTIONS --safe --cubical --lossy-unification #-}
module PropositionalTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat  hiding (elim)
open import Cubical.Data.Prod hiding (map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence
import ShiftAlgebra as Shift


private
  variable
    ℓ ℓ' : Level


module _ (X : Type ℓ) where


  data Word : ℕ → Type ℓ where
    shift  : {n : ℕ} → Word n → Word (suc n)
    ∣_∣    : X → Word 0
    squash : {n : ℕ} (a b : Word n) → shift a ≡ shift b
    comm-squash : {n : ℕ} (a b : Word n) →
      Square refl refl (cong shift (squash a b)) (squash (shift a) (shift b))

  open Sequence

  Word∙ : Sequence ℓ
  Word∙ .obj = Word
  Word∙ .map = shift

  Word∞ = SeqColim Word∙

  open Coh Word∙


  ∣_∣∞ : X → Word∞
  ∣ x ∣∞ = incl ∣ x ∣


  Args-squash : ℕ → Type ℓ
  Args-squash n = Word n × Word n

  shift-squash : {n : ℕ} → Args-squash n → Args-squash (suc n)
  shift-squash (a , b) = shift a , shift b

  data Argsω-squash : Type ℓ where
    incl : {n : ℕ} → Args-squash n → Argsω-squash
    push : {n : ℕ} (x : Args-squash n) → incl x ≡ incl (shift-squash x)

  take1 : Argsω-squash → Word∞
  take1 (incl (a , b))   = incl a
  take1 (push (a , b) i) = push a i

  take2 : Argsω-squash → Word∞
  take2 (incl (a , b))   = incl b
  take2 (push (a , b) i) = push b i

  pushCoh-squash : {n : ℕ} (a b : Word n) (i : I) (𝓲 𝓳 : I) → Word∞
  pushCoh-squash a b i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-shift a 𝓲 𝓳
      ; (i = i1) → pushCoh-shift b 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (squash a b i)
      ; (𝓲 = i1) → incl (comm-squash a b i 𝓳) })
      (inS (push (squash a b i) 𝓲))


  squash∞ : (r : Argsω-squash) → shift∞ (take1 r) ≡ shift∞ (take2 r)
  squash∞ (incl (a , b))   i = incl (squash a b i)
  squash∞ (push (a , b) 𝓲) i = pushCoh-squash a b i 𝓲 i1


  module ThickElim
    (P : Word∞ → Type ℓ')
    (shiftP : (w : Word∞) → P w → P (shift∞ w))
    (pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p))
    (∣_∣P : (x : X) → P ∣ x ∣∞)
    (squashP : (r : Argsω-squash) (u : P (take1 r)) (v : P (take2 r))
      → PathP (λ i → P (squash∞ r i)) (shiftP _ u) (shiftP _ v))
    where


    open CohP P shiftP pushP


    pushCohP-squash : {n : ℕ} (a b : Word n) (u : P (incl a)) (v : P (incl b))
      (i : I) (𝓲 𝓳 : I) → P (pushCoh-squash a b i 𝓲 𝓳)
    pushCohP-squash a b u v i 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-squash a b i 𝓲 𝓳)) (λ 𝓲 → λ
        { (i = i0) → pushCohP-shift _ u 𝓲 𝓳
        ; (i = i1) → pushCohP-shift _ v 𝓲 𝓳
        -------------
        ; (𝓳 = i0) → pushP _ (squashP (incl (a , b)) u v i) 𝓲
        ; (𝓳 = i1) → squashP (push (a , b) 𝓲) (pushP _ u 𝓲) (pushP _ v 𝓲) i })
        (inS (squashP (incl (a , b)) u v i)) 𝓲


    elim₀ : {n : ℕ} (w : Word n) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀ ∣ x ∣          = ∣ x ∣P
    elim₀ (squash a b 𝓳) = squashP (incl (a , b)) (elim₀ a) (elim₀ b) 𝓳
    elim₀ (comm-squash a b i 𝓳) = pushCohP-squash a b (elim₀ a) (elim₀ b) i i1 𝓳

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


    elimβ-squash : (x : Argsω-squash)
      → SquareP (λ i _ → P (squash∞ x i))
          (elimβ-shift (take1 x)) (elimβ-shift (take2 x))
          (cong elim (squash∞ x)) (squashP x (elim (take1 x)) (elim (take2 x)))
    elimβ-squash (incl (a , b))   _ = refl
    elimβ-squash (push (a , b) 𝓲) i 𝓴 =
      comp (λ 𝓳 → P (pushCoh-squash a b i 𝓲 𝓳)) (λ 𝓳 → λ
        { (i = i0) → pushCohP-shift _ (elim₀ a) 𝓲 (𝓳 ∧ 𝓴)
        ; (i = i1) → pushCohP-shift _ (elim₀ b) 𝓲 (𝓳 ∧ 𝓴)
        -------------
        ; (𝓲 = i0) → elim₀ (squash a b i)
        ; (𝓲 = i1) → elim₀ (comm-squash a b i 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-squash a b i 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-squash a b (elim₀ a) (elim₀ b) i 𝓲 𝓳 })
       (elim (push (squash a b i) 𝓲))
