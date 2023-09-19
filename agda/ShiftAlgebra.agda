{-# OPTIONS --safe --cubical --lossy-unification #-}
module ShiftAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)


private
  variable
    ℓ ℓ' : Level


data Word : ℕ → Type where
  shift : {n : ℕ} → Word n → Word (suc n)
  base  : Word 0

open Sequence

Word∙ : Sequence ℓ-zero
Word∙ .obj = Word
Word∙ .map = shift

Word∞ = SeqColim Word∙


isContrWord∞ : isContr Word∞
isContrWord∞ .fst = incl base
isContrWord∞ .snd = contr
  where
  contr₀ : {n : ℕ} (x : Word n) → incl base ≡ incl x
  contr₀  base     = refl
  contr₀ (shift w) = contr₀ w ∙ push w

  contr : (x : Word∞) → incl base ≡ x
  contr (incl  w)   = contr₀ w
  contr (push w i) = compPath-filler (contr₀ w) (push w) i


extendWord∞ : {φ : I} (u : Partial φ Word∞) → Word∞ [ φ ↦ u ]
extendWord∞ = extend isContrWord∞ _


shift∞ : Word∞ → Word∞
shift∞ (incl w)   = incl (shift w)
shift∞ (push w i) = push (shift w) i

push∞ : (w : Word∞) → w ≡ shift∞ w
push∞ (incl w)     = push w
push∞ (push w i) j = hcomp (λ k → λ
  { (i = i0) → push w (j ∨ ~ k)
  ; (i = i1) → push (shift w) (j ∧ k)
  ; (j = i0) → push w (i ∨ ~ k)
  ; (j = i1) → push (shift w) (i ∧ k) })
  (incl (shift w))


push²∞ : (w : Word∞) → w ≡ shift∞ (shift∞ w)
push²∞ _ = push∞ _ ∙ push∞ _


{-
push²∞ : (w : Word∞) → w ≡ shift∞ (shift∞ w)
push²∞ w i = push∞ (push∞ w i) i
-}

data WordP∞ : Word∞ → Type where
  -- shift : (w : Word∞) (p : WordP∞ w) → WordP∞ w → WordP∞ (shift∞ w)
  -- push  : (w : Word∞) (p : WordP∞ w) → PathP (λ i → WordP∞ (push∞ w i)) p (shift _ p)
  shift₀ : {n : ℕ} (w : Word n) → WordP∞ (incl w) → WordP∞ (shift∞ (incl w))
  shift₁ : {n : ℕ} (w : Word n) →
    PathP (λ i → WordP∞ (push w i) → WordP∞ (shift∞ (push w i))) (shift₀ w) (shift₀ (shift w))
  push₀  :  {n : ℕ} (w : Word n) (p : WordP∞ (incl w)) →
    PathP (λ i → WordP∞ (push w i)) p (shift₀ _ p)
  push₁  :  {n : ℕ} (w : Word n) →
    PathP (λ i → (p : WordP∞ (push w i))
      → PathP (λ j → WordP∞ (push∞ (push w i) j)) p (shift₁ _ i p))
      (push₀ _) (push₀ _)
  base   : WordP∞ (incl base)


shiftP : (w : Word∞) → WordP∞ w → WordP∞ (shift∞ w)
shiftP (incl w)   = shift₀ _
shiftP (push w i) = shift₁ _ i

pushP : (w : Word∞) (p : WordP∞ w) → PathP (λ i → WordP∞ (push∞ w i)) p (shiftP _ p)
pushP (incl w)   = push₀ _
pushP (push w i) = push₁ _ i

push²P : (w : Word∞) (p : WordP∞ w) → PathP (λ i → WordP∞ (push²∞ w i)) p (shiftP _ (shiftP _ p))
push²P w p i =
  comp (λ j → WordP∞ (compPath-filler (push∞ w) (push∞ (shift∞ w)) j i)) (λ j → λ
    { (i = i0) → p
    ; (i = i1) → pushP _ (shiftP _ p) j })
    (pushP _ p i)
 -- pushP _ (pushP _ p i) i


isContrΣWordP∞ : isContr (Σ _ WordP∞)
isContrΣWordP∞ .fst = _ , base
isContrΣWordP∞ .snd (x , p) = contrP x p
  where
  contrP : (x : Word∞) (p : WordP∞ x) → (_ , base) ≡ (x , p)
  contrP _  base         = refl
  contrP _ (shift₀ _   p) = contrP _ p ∙ (λ i → _ , pushP _ p i)
  contrP _ (shift₁ _ i p) = contrP _ p ∙ (λ i → _ , pushP _ p i)
  contrP _ (push₀  _   p i) = compPath-filler (contrP _ p) (λ i → _ , pushP _ p i) i
  contrP _ (push₁  _ j p i) = compPath-filler (contrP _ p) (λ i → _ , pushP _ p i) i

extendΣWordP∞ : {φ : I} (u : Partial φ (Σ _ WordP∞)) → Σ _ WordP∞ [ φ ↦ u ]
extendΣWordP∞ = extend isContrΣWordP∞ _

isContrWordP∞ : (w : Word∞) → isContr (WordP∞ w)
isContrWordP∞ w .fst = transport (λ i → WordP∞ (isContrWord∞ .snd w i)) base
isContrWordP∞ w .snd p j =
  comp (λ i → WordP∞ (square i j)) (λ i → λ
    { (j = i0) → transport-filler (λ i → WordP∞ (isContrWord∞ .snd w i)) base i
    ; (j = i1) → path i .snd })
    (base)
  where
  path : (i : I) → Σ _ WordP∞
  path i = outS (extendΣWordP∞ λ
    { (i = i0) → _ , base
    ; (i = i1) → _ , p })

  square : (i j : I) → Word∞
  square i j = outS (extendWord∞ λ
    { (i = i0) → incl base
    ; (i = i1) → w
    ; (j = i0) → isContrWord∞ .snd w i
    ; (j = i1) → path i .fst })



extendWordP∞ : {φ : I} (w : Word∞) (u : Partial φ (WordP∞ w)) → (WordP∞ w) [ φ ↦ u ]
extendWordP∞ w = extend (isContrWordP∞ w) _


elim₀ : {n : ℕ} (w : Word n) → WordP∞ (incl w)
elim₀ (shift w) = shift₀ _ (elim₀ w)
elim₀  base     = base

elim : (w : Word∞) → WordP∞ w
elim (incl w)   = elim₀ w
elim (push w 𝓲) = push₀ _ (elim₀ w) 𝓲


pushCohP-shift-square :
  SquareP (λ i j → WordP∞ (push (shift base) i))
      refl refl (pushP _ (shiftP _ base)) (λ i → shiftP _ (pushP _ base i))
pushCohP-shift-square i j = outS (extendWordP∞ (push (shift base) i) λ
    { (i = i0) → shiftP _ base
    ; (i = i1) → shiftP _ (shiftP _ base)
    ; (j = i0) → pushP  _ (shiftP _ base) i
    ; (j = i1) → shiftP _ (pushP  _ base i) })


pushCohP-shift-shift-square :
  SquareP (λ i j → WordP∞ (push (shift (shift base)) i))
      refl refl (pushP _ (shiftP _ (shiftP _ base))) (λ i → shiftP _ (shiftP _ (pushP _ base i)))
pushCohP-shift-shift-square i j = outS (extendWordP∞ (push (shift (shift base)) i) λ
    { (i = i0) → shiftP _ (shiftP _ base)
    ; (i = i1) → shiftP _ (shiftP _ (shiftP _ base))
    ; (j = i0) → pushP _ (shiftP _ (shiftP _ base)) i
    ; (j = i1) → shiftP _ (shiftP _ (pushP _ base i)) })


elim-push-cube : (i j k : I) → WordP∞ (push∞ (push base i) k)
elim-push-cube i j k =
  outS (extendWordP∞ (push∞ (push base i) k) λ
    { (i = i0) → pushP _ base k
    ; (i = i1) → pushP _ (shiftP _ base) k
    ; (j = i0) → elim (push∞ (push base i) k)
    ; (j = i1) → pushP _ (pushP _ base i) k
    ; (k = i0) → pushP _ base i
    ; (k = i1) → pushCohP-shift-square i j })


elim-push-push-cube : (i j k : I) → WordP∞ (push²∞ (push base i) k)
elim-push-push-cube i j k =
  outS (extendWordP∞ (push²∞ (push base i) k) λ
    { (i = i0) → push²P _ base k
    ; (i = i1) → push²P _ (shiftP _ base) k
    ; (j = i0) → elim (push²∞ (push base i) k)
    ; (j = i1) → push²P _ (pushP _ base i) k
    ; (k = i0) → pushP _ base i
    ; (k = i1) → pushCohP-shift-shift-square i j })
