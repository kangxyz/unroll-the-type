{-# OPTIONS --safe --cubical #-}
module Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence

private
  variable
    ℓ : Level


data Word : ℕ → Type where
  shift : {n : ℕ} → Word n → Word (suc n)
  base  : Word 0
  cons  : {n : ℕ} → Word n → Word (suc n)
  comm-cons : {n : ℕ} (w : Word n) → shift (cons w) ≡ cons (shift w)

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


module ThickElim
  (P : Word∞ → Type ℓ)
  (shiftP : (w : Word∞) → P w → P (shift∞ w))
  (pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p))
  (baseP : P (base∞))
  (consP : (w : Word∞) → P w → P (cons∞ w))
  where

  pushCohP-cons : {n : ℕ} (w : Word n) (p : P (incl w))
    (𝓲 𝓳 : I) → P (pushCoh-cons w 𝓲 𝓳)
  pushCohP-cons w p 𝓲 𝓳 =
    fill (λ 𝓲 → P (pushCoh-cons w 𝓲 𝓳)) (λ 𝓲 → λ
      { (𝓳 = i0) → pushP _ (consP _ p) 𝓲
      ; (𝓳 = i1) → consP _ (pushP _ p 𝓲) })
      (inS (consP _ p)) 𝓲

  elim₀ : {n : ℕ} (w : Word n) → P (incl w)
  elim₀ (shift w) = shiftP _ (elim₀ w)
  elim₀  base = baseP
  elim₀ (cons w) = consP _ (elim₀ w)
  elim₀ (comm-cons w 𝓳) = pushCohP-cons w (elim₀ w) i1 𝓳

  elim : (w : Word∞) → P w
  elim (incl w)   = elim₀ w
  elim (push w i) = pushP _ (elim₀ w) i

  elimβ-base : elim base∞ ≡ baseP
  elimβ-base = refl

  elimβ-cons : (w : Word∞) → elim (cons∞ w) ≡ consP _ (elim w)
  elimβ-cons (incl w)     = refl
  elimβ-cons (push w 𝓲) 𝓴 =
    comp (λ 𝓳 → P (pushCoh-cons w 𝓲 𝓳)) (λ 𝓳 → λ
      { (𝓲 = i0) → elim₀ (cons w)
      ; (𝓲 = i1) → elim₀ (comm-cons w 𝓳)
   -- ; (𝓴 = i0) → elim (pushCoh-cons w 𝓲 𝓳)
      ; (𝓴 = i1) → pushCohP-cons w (elim₀ w) 𝓲 𝓳 })
      (elim (push (cons w) 𝓲))


module ThinElim
  (P : Word∞ → Type ℓ)
  (baseP : P (base∞))
  (consP : (w : Word∞) → P w → P (cons∞ w))
  where

  transport-push∞ : (w : Word∞) (p : P w) (i : I) → P (push∞ w i)
  transport-push∞ w p i = transport-filler (λ i → P (push∞ w i)) p i

  shiftP : (w : Word∞) → P w → P (shift∞ w)
  shiftP w p = transport-push∞ w p i1

  pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p)
  pushP w p i = transport-push∞ w p i

  module Thick = ThickElim P shiftP pushP baseP consP

  elim : (w : Word∞) → P w
  elim = Thick.elim

  elimβ-base : elim base∞ ≡ baseP
  elimβ-base = refl

  elimβ-cons : (w : Word∞) → elim (cons∞ w) ≡ consP _ (elim w)
  elimβ-cons = Thick.elimβ-cons
