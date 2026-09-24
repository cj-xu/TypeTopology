Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Examples of ordinal-induced successors

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.InducedSuccessorExamples (ua : Univalence) where

open import MLTT.Spartan
import Ordinals.CantorNormalForm
import Ordinals.OrdinalOfOrdinalsWithProperty
open import Ordinals.InducedSuccessor ua
open import Ordinals.Successors ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.AdditionProperties ua
 using (𝟘ₒ-least-⊴; 𝟘ₒ-left-neutral)
open import UF.UA-FunExt using (Univalence-gives-FunExt)
open import Ordinals.Arithmetic (Univalence-gives-FunExt ua)
 using (𝟘ₒ; 𝟙ₒ)
open import UF.ClassicalLogic
open import UF.Subsingletons


\end{code}

■ Agreement with the induced successor

If A satisfies P, its initial segment in Pₒ represents A.  The direct
successor of A equals the successor of this initial segment induced by Pₒ.
The initial-segment comparison lemma identifies the membership conditions,
and both constructions inherit the same strict order.

\begin{code}

module WithProperty
        {𝓤 : Universe}
        (P : Ordinal 𝓤 → 𝓤 ⁺ ̇ )
        (P-is-prop : (A : Ordinal 𝓤) → is-prop (P A))
        (P-is-hereditary : (A C : Ordinal 𝓤) → P A → C ⊲ A → P C)
       where

 open Ordinals.OrdinalOfOrdinalsWithProperty.WithProperty ua
       P P-is-prop P-is-hereditary
  using (Pₒ; direct-succ; ↓-⊴-iff-⊴)

 module Induced = InducedSuccessor Pₒ

 direct-succ-equals-induced-succ : (A : Ordinal 𝓤) (p : P A)
                               → direct-succ A
                                 ＝ Induced.induced-succ (Pₒ ↓ (A , p))
 direct-succ-equals-induced-succ A p = ⊴-antisym D I forward backward
  where
   D = direct-succ A
   I = Induced.induced-succ (Pₒ ↓ (A , p))

   f : ⟨ D ⟩ → ⟨ I ⟩
   f (C , q , h) = (C , q) , pr₂ (↓-⊴-iff-⊴ (C , q) (A , p)) h

   g : ⟨ I ⟩ → ⟨ D ⟩
   g ((C , q) , h) = C , q , pr₁ (↓-⊴-iff-⊴ (C , q) (A , p)) h

   fg : (y : ⟨ I ⟩) → f (g y) ＝ y
   fg y = to-subtype-＝ (λ x → ⊴-is-prop-valued (Pₒ ↓ x)
                              (Pₒ ↓ (A , p))) refl

   gf : (x : ⟨ D ⟩) → g (f x) ＝ x
   gf x = to-subtype-＝
           (λ C → ×-is-prop (P-is-prop C) (⊴-is-prop-valued C A)) refl

   forward : D ⊴ I
   forward = f , (λ x y l → g y , l , fg y) , (λ x y l → l)

   backward : I ⊴ D
   backward = g , (λ x y l → f y , l , gf y) , (λ x y l → l)

\end{code}

■ Cantor normal forms

We take the ordinal Cnfₒ of Cantor normal forms (CNFs) as the base.

Its trichotomous order and internal successor supply the conditions needed for
the general characterization theorems.

\begin{code}

module CantorNormalForms where

 module CNF = Ordinals.CantorNormalForm
 open CNF using (Cnf; Cnfₒ)
 open InducedSuccessor Cnfₒ public

\end{code}

Recall that the weak order of CNFs has mixed transitivity and splits into
strict comparison or equality, and that the every CNF has a strong and exact
successor.

\begin{code}

 mixed-transitivity : Mixed-transitivity
 mixed-transitivity = CNF.≼-<-gives-<

 weak-order-splits : Weak-order-splits
 weak-order-splits x y h = split (CNF.≼-gives-≦ h)
  where
   split : x CNF.≦ y → (x ≺ᴮ y) + (x ＝ y)
   split (inl l) = inl l
   split (inr e) = inr (e ⁻¹)

 strong-successor : calc-strong-succ CNF.succ
 strong-successor = CNF.succ-is-strong-succ ua

 exact-successors : Has-exact-successors
 exact-successors x = CNF.succ x , CNF.succ-is-exact-succ ua x

 bounded-elements-have-successors : Bounded-elements-have-successors
 bounded-elements-have-successors x y h
  = CNF.succ x , strong-succ-gives-succ (CNF.succ x) x (strong-successor x)

\end{code}

Therefore, the successor induced by Cnfₒ has all the desired properties.

\begin{code}

 relative-leastness : Induced-succ-relative-leastness
 relative-leastness
  = mixed-transitivity-gives-induced-succ-relative-leastness mixed-transitivity

 commutes-with-successor : Induced-succ-commutes-with CNF.succ
 commutes-with-successor
  = mixed-transitivity-gives-induced-succ-commutation
     CNF.succ strong-successor mixed-transitivity

 strict-monotonicity : Induced-succ-strict-monotonicity
 strict-monotonicity
  = mixed-transitivity-and-bounded-successors-give-strict-monotonicity
     (mixed-transitivity , bounded-elements-have-successors)

 closure : Induced-succ-closure
 closure = has-exact-successors-gives-induced-succ-closure exact-successors

\end{code}

For inputs strictly below Cnfₒ, the induced successor coincides with the thin
successor.  However, for fat successor, this is equivalent to excluded middle.

\begin{code}

 below-thin : Induced-succ-below-thin
 below-thin = weak-order-splits-gives-induced-succ-⊴-thin-succ weak-order-splits

 induced-succ-equals-thin : (A : Ordinal 𝓤₀) → A ⊲ Cnfₒ
                          → induced-succ A ＝ thin-succ A
 induced-succ-equals-thin A h
  = ⊴-antisym (induced-succ A) (thin-succ A)
     (below-thin A h) (thin-succ-⊴-induced-succ A h)

 private
  zero-segment : Cnfₒ ↓ CNF.𝟎 ＝ 𝟘ₒ
  zero-segment = ⊴-antisym (Cnfₒ ↓ CNF.𝟎) 𝟘ₒ
                  (f , (λ u → 𝟘-elim (f u)) , (λ u → 𝟘-elim (f u)))
                  (𝟘ₒ-least-⊴ (Cnfₒ ↓ CNF.𝟎))
   where
    f : (Σ x ꞉ Cnf , x CNF.< CNF.𝟎) → 𝟘
    f (x , ())

  one-below-base : 𝟙ₒ ⊲ Cnfₒ
  one-below-base = CNF.succ CNF.𝟎 , (q ⁻¹)
   where
    q : Cnfₒ ↓ CNF.succ CNF.𝟎 ＝ 𝟙ₒ
    q = commutes-with-successor CNF.𝟎
        ∙ induced-succ-equals-thin (Cnfₒ ↓ CNF.𝟎) (CNF.𝟎 , refl)
        ∙ ap thin-succ zero-segment ∙ 𝟘ₒ-left-neutral 𝟙ₒ

 fat-below-induced-gives-EM : Fat-succ-below-induced → EM 𝓤₀
 fat-below-induced-gives-EM comparison
  = fat-succ-one-⊴-thin-succ-one-gives-EM
     (⊴-trans (fat-succ 𝟙ₒ) (induced-succ 𝟙ₒ) (thin-succ 𝟙ₒ)
       (comparison 𝟙ₒ one-below-base) (below-thin 𝟙ₒ one-below-base))

 EM-gives-fat-below-induced : EM 𝓤₀ → Fat-succ-below-induced
 EM-gives-fat-below-induced em A h
  = transport⁻¹ (fat-succ A ⊴_) (induced-succ-equals-thin A h)
     (EM-gives-fat-succ-⊴-thin-succ em A)

 fat-below-induced-iff-EM : Fat-succ-below-induced ↔ EM 𝓤₀
 fat-below-induced-iff-EM
  = fat-below-induced-gives-EM , EM-gives-fat-below-induced

 external-mixed-transitivity-iff-EM
  : External-mixed-transitivity-below-base ↔ EM 𝓤₀
 external-mixed-transitivity-iff-EM
  = ↔-trans
     (↔-sym fat-succ-⊴-induced-succ-iff-external-mixed-transitivity-below-base)
     fat-below-induced-iff-EM

\end{code}
