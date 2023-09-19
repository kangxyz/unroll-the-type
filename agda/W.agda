{-# OPTIONS --safe --cubical #-}
module W where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence


private
  variable
    ℓ ℓ' ℓ'' : Level


module _
  (A : Type ℓ) (B : A → Type ℓ') where


  data W : Type (ℓ-max ℓ ℓ') where
    node : (a : A) (t : (b : B a) → W) → W


  data Word : ℕ → Type (ℓ-max ℓ ℓ') where
    shift : {n : ℕ} → Word n → Word (suc n)
    node  : {n : ℕ} (a : A) (t : (b : B a) → Word n) → Word (suc n)
    comm-node : {n : ℕ} (a : A) (t : (b : B a) → Word n)
      → shift (node a t) ≡ node a (λ b → shift (t b))

  open Sequence

  Word∙ : Sequence (ℓ-max ℓ ℓ')
  Word∙ .obj = Word
  Word∙ .map = shift

  Word∞ = SeqColim Word∙

  open Coh Word∙


  Args-node : (a : A) → ℕ → Type (ℓ-max ℓ ℓ')
  Args-node a n = (b : B a) → Word n

  shift-node : {a : A} {n : ℕ} → Args-node a n → Args-node a (suc n)
  shift-node f b = shift (f b)

  data Argsω-node (a : A) : Type (ℓ-max ℓ ℓ') where
    incl : {n : ℕ} → Args-node a n → Argsω-node a
    push : {n : ℕ} (f : Args-node a n) → incl f ≡ incl (shift-node f)

  _*_ : {a : A} → Argsω-node a → B a → Word∞
  incl t   * b = incl (t b)
  push t i * b = push (t b) i

  to : (a : A) → Argsω-node a → B a → Word∞
  to a t b = t * b

  pushCoh-node : (a : A) {n : ℕ} (f : B a → Word n) (𝓲 𝓳 : I) → Word∞
  pushCoh-node a f 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (node a f)
      ; (𝓲 = i1) → incl (comm-node a f 𝓳) })
      (inS (push (node a f) 𝓲))

  node∞ : (a : A) (t : Argsω-node a) → Word∞
  node∞ a (incl f)   = incl (node a f)
  node∞ a (push f 𝓲) = pushCoh-node a f 𝓲 i1


  module ThickElim
    (P : Word∞ → Type ℓ'')
    (shiftP : (w : Word∞) → P w → P (shift∞ w))
    (pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p))
    (nodeP : (a : A) (t : Argsω-node a) (f : (b : B a) → P (t * b)) → P (node∞ a t))
    where

    pushCohP-node : (a : A) {n : ℕ} (t : B a → Word n) (p : (b : B a) → P (incl (t b)))
      (𝓲 𝓳 : I) → P (pushCoh-node a t 𝓲 𝓳)
    pushCohP-node a t p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-node a t 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (nodeP _ (incl t) p) 𝓲
        ; (𝓳 = i1) → nodeP _ (push t 𝓲) (λ b → pushP _ (p b) 𝓲) })
        (inS (nodeP _ (incl t) p)) 𝓲

    elim₀ : {n : ℕ} (w : Word n) → P (incl w)
    elim₀ (shift w)   = shiftP _ (elim₀ w)
    elim₀ (node  a t) = nodeP _ (incl t) (λ b → elim₀ (t b))
    elim₀ (comm-node a t 𝓳) = pushCohP-node a t (λ b → elim₀ (t b)) i1 𝓳

    elim : (w : Word∞) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲

    elimβ-node : (a : A) (t : Argsω-node a) → elim (node∞ a t) ≡ nodeP _ t (λ b → elim (t * b))
    elimβ-node a (incl t)     = refl
    elimβ-node a (push t 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-node a t 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (node a t)
        ; (𝓲 = i1) → elim₀ (comm-node a t 𝓳)
     -- ; (𝓴 = i0) → elim (pushCoh-node a t 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-node a t (λ b → elim₀ (t b)) 𝓲 𝓳 })
        (elim (push (node a t) 𝓲))


  module ThinElim
    (P : Word∞ → Type ℓ'')
    (nodeP : (a : A) (t : Argsω-node a) (f : (b : B a) → P (t * b)) → P (node∞ a t))
    where

    transport-push∞ : (w : Word∞) (p : P w) (i : I) → P (push∞ w i)
    transport-push∞ w p i = transport-filler (λ i → P (push∞ w i)) p i

    shiftP : (w : Word∞) → P w → P (shift∞ w)
    shiftP w p = transport-push∞ w p i1

    pushP : (w : Word∞) (p : P w) → PathP (λ i → P (push∞ w i)) p (shiftP _ p)
    pushP w p i = transport-push∞ w p i

    module Thick = ThickElim P shiftP pushP nodeP

    elim : (w : Word∞) → P w
    elim = Thick.elim

    elimβ-node : (a : A) (t : Argsω-node a) → elim (node∞ a t) ≡ nodeP _ t (λ b → elim (t * b))
    elimβ-node = Thick.elimβ-node


  module _
    (is-comp : (a : A) → isEquiv (to a))
    where


    from : (a : A) → (B a → Word∞) → Argsω-node a
    from a = funIsEq (invEquiv (_ , is-comp a) .snd)

    from-to : (a : A) (t : Argsω-node a) → from a (to a t) ≡ t
    from-to a = secIsEq (invEquiv (_ , is-comp a) .snd)

    to-from : (a : A) (t : _) → to a (from a t) ≡ t
    to-from a = retIsEq (invEquiv (_ , is-comp a) .snd)

    comm-square : (a : A) (t : _) → from-to a (from a t) ≡ cong (from a) (to-from a t)
    comm-square a = commPathIsEq (invEquiv (_ , is-comp a) .snd)


    node∞' : (a : A) (t : B a → Word∞) → Word∞
    node∞' a t = node∞ a (from a t)


    module _
      (P : Word∞ → Type ℓ'')
      (nodeP' : (a : A) (t : B a → Word∞) (f : (b : B a) → P (t b)) → P (node∞' a t))
      where

      n-push : (a : A) (t : Argsω-node a) (f : (b : B a) → P (t * b)) (i : I) → P (node∞ a (from-to a t i))
      n-push a t f i = transport-filler (λ i → P (node∞ a (from-to a t i))) (nodeP' a (to a t) f) i

      module Thin = ThinElim P (λ a t f → n-push a t f i1)

      elim : (w : Word∞) → P w
      elim = Thin.elim

      elimβ-node : (a : A) (t : B a → Word∞) → elim (node∞' a t) ≡ nodeP' _ t (λ b → elim (t b))
      elimβ-node a t = Thin.elimβ-node a (from a t) ∙
        (λ i →
        comp (λ j → P (node∞ a (comm-square a t i j))) (λ j → λ
          { (i = i0) → n-push a (from a t)  (λ b → elim (from a t * b)) j
          ; (i = i1) → nodeP' _ (to-from a t j) (λ b → elim (to-from a t j b)) })
          (nodeP' _ (to a (from a t)) (λ b → elim (from a t * b))))
