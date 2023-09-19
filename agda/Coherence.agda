{-

The Coherence Machine

-}
{-# OPTIONS --safe --cubical #-}
module Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import ShiftAlgebra
  renaming (shift∞ to S-shift∞ ; push∞  to S-push∞
          ; elim₀  to S-elim₀  ; elim   to S-elim
          ; push²∞ to S-push²∞ ; push²P to S-push²P)

private
  variable
    ℓ ℓ' : Level


module Coh
  (X : Sequence ℓ)
  where

  open Sequence


  module _ {n : ℕ} (x : X .obj n) where

    solve₀ : {m : ℕ} → Word m → X .obj (m + n)
    solve₀  base     = x
    solve₀ (shift w) = X .map (solve₀ w)

    solve : Word∞ → SeqColim X
    solve (incl w)   = incl (solve₀ w)
    solve (push w i) = push (solve₀ w) i


  shift∞ : SeqColim X → SeqColim X
  shift∞ (incl w)   = incl (X .map w)
  shift∞ (push w 𝓲) = push (X .map w) 𝓲

  push∞ : (w : SeqColim X) → w ≡ shift∞ w
  push∞ (incl w)     = push w
  push∞ (push w 𝓲) j = solve w (S-push∞ (push base 𝓲) j)

  pushCoh-shift : {n : ℕ} (x : X .obj n) (𝓲 𝓳 : I) → SeqColim X
  pushCoh-shift x 𝓲 𝓳 = push (X .map x) 𝓲

  pushCoh-shift-shift : {n : ℕ} (x : X .obj n) (𝓲 𝓳 : I) → SeqColim X
  pushCoh-shift-shift x 𝓲 𝓳 = push (X .map (X .map x)) 𝓲

  push²∞ : (w : SeqColim X) → w ≡ shift∞ (shift∞ w)
  push²∞ (incl w)   j = solve w (S-push²∞ (incl base) j)
  push²∞ (push w 𝓲) j = solve w (S-push²∞ (push base 𝓲) j)

{-
  push²∞ : (w : SeqColim X) → w ≡ shift∞ (shift∞ w)
  push²∞ _ = push∞ _ ∙ push∞ _
-}

  module CohP
    (P : SeqColim X → Type ℓ')
    (shiftP : (x : SeqColim X) → P x → P (shift∞ x))
    (pushP  : (x : SeqColim X) (p : P x) → PathP (λ i → P (push∞ x i)) p (shiftP _ p))
    where


    module _ {n : ℕ} (x : X .obj n) (p : P (incl x)) where

      solveP : {w : Word∞} (q : WordP∞ w) → P (solve x w)
      solveP  base = p
      solveP (shift₀ _   q)  = shiftP _ (solveP q)
      solveP (shift₁ _ i q)  = shiftP _ (solveP q)
      solveP (push₀ _   q i) = pushP  _ (solveP q) i
      solveP (push₁ _ j q i) = pushP  _ (solveP q) i


    pushCohP-shift : {n : ℕ} (x : X .obj n) (p : P (incl x))
      → SquareP (λ 𝓲 𝓳 → P (pushCoh-shift x 𝓲 𝓳))
          refl refl (pushP _ (shiftP _ p)) (λ i → shiftP _ (pushP _ p i))
    pushCohP-shift x p i j = solveP x p (pushCohP-shift-square i j)

    pushCohP-shift-shift : {n : ℕ} (x : X .obj n) (p : P (incl x))
      → SquareP (λ 𝓲 𝓳 → P (pushCoh-shift-shift x 𝓲 𝓳))
          refl refl (pushP _ (shiftP _ (shiftP _ p))) (λ i → shiftP _ (shiftP _ (pushP _ p i)))
    pushCohP-shift-shift x p i j = solveP x p (pushCohP-shift-shift-square i j)

{-
    push²P : (x : SeqColim X) (p : P x) → PathP (λ i → P (push²∞ x i)) p (shiftP _ (shiftP _ p))
    push²P (incl x)   p i = solveP x p (S-push²P _ base i)
    push²P (push x j) p i = solveP x _ (S-push²P (push x j) _ i)
-}
  {-
      comp (λ j → P (compPath-filler (push∞ x) (push∞ (shift∞ x)) j i)) (λ j → λ
        { (i = i0) → p
        ; (i = i1) → pushP _ (shiftP _ p) j })
        (pushP _ p i) -}



{-
    module ThickElim
      (elim₀ : {n : ℕ} (x : X .obj n) → P (incl x))
      where

      elim : (x : SeqColim X) → P x
      elim (incl x)   = elim₀ x
      elim (push x 𝓲) = pushP _ (elim₀ x) 𝓲
-}
