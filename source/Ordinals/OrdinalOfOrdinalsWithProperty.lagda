Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
24 September 2026

Ordinals satisfying a hereditary property

A proposition-valued property inherited by strict predecessors determines
an ordinal of ordinals satisfying that property.  Its internal weak order
agrees with weak ordinal comparison.  We also construct the ordinal of
ordinals satisfying the property and weakly below a given ordinal.  Under
resizing assumptions, we give an order-isomorphic small construction.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.OrdinalOfOrdinalsWithProperty (ua : Univalence) where

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Equivalence
open import Ordinals.OrdinalOfOrdinals ua
 hiding (⊴-gives-≼)
 renaming (≼-gives-⊴ to ordinal-≼-gives-⊴)
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Subsingletons
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets-Properties
open import UF.Size
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.UA-FunExt using (Univalence-gives-FunExt)
open import Ordinals.WellOrderTransport (Univalence-gives-FunExt ua)

module WithProperty
        {𝓤 : Universe}
        (P : Ordinal 𝓤 → 𝓤 ⁺ ̇ )
        (P-is-prop : (A : Ordinal 𝓤) → is-prop (P A))
        (P-is-hereditary : (A C : Ordinal 𝓤) → P A → C ⊲ A → P C)
       where

 Ordinals-with-property : 𝓤 ⁺ ̇
 Ordinals-with-property = Σ A ꞉ Ordinal 𝓤 , P A

 property-order : Ordinals-with-property → Ordinals-with-property → 𝓤 ⁺ ̇
 property-order = subtype-order (OO 𝓤) P

 property-order-is-extensional : is-extensional property-order
 property-order-is-extensional (A , p) (B , q) f g
  = to-subtype-＝ P-is-prop
     (⊲-is-extensional A B
       (λ C h → f (C , P-is-hereditary A C p h) h)
       (λ C h → g (C , P-is-hereditary B C q h) h))

 property-order-is-well-order : is-well-order property-order
 property-order-is-well-order
  = subtype-order-is-prop-valued (OO 𝓤) P ,
    subtype-order-is-well-founded (OO 𝓤) P ,
    property-order-is-extensional ,
    subtype-order-is-transitive (OO 𝓤) P

 Pₒ : Ordinal (𝓤 ⁺)
 Pₒ = Ordinals-with-property , property-order , property-order-is-well-order

\end{code}

Every predecessor of an ordinal satisfying P also satisfies P.  Consequently,
comparison of predecessors within Pₒ is equivalent to comparison of all
ordinal predecessors.

\begin{code}

 ≼-gives-⊴ : (x y : ⟨ Pₒ ⟩) → x ≼⟨ Pₒ ⟩ y → pr₁ x ⊴ pr₁ y
 ≼-gives-⊴ (A , p) (B , q) h
  = ordinal-≼-gives-⊴ A B
     (λ C k → h (C , P-is-hereditary A C p k) k)

 ⊴-gives-≼ : (x y : ⟨ Pₒ ⟩) → pr₁ x ⊴ pr₁ y → x ≼⟨ Pₒ ⟩ y
 ⊴-gives-≼ (A , p) (B , q) h (C , r) k = ⊲-⊴-gives-⊲ C A B k h

 ≼-iff-⊴ : (x y : ⟨ Pₒ ⟩) → (x ≼⟨ Pₒ ⟩ y ↔ pr₁ x ⊴ pr₁ y)
 ≼-iff-⊴ x y = ≼-gives-⊴ x y , ⊴-gives-≼ x y

 ↓-⊴-iff-⊴ : (x y : ⟨ Pₒ ⟩)
           → ((Pₒ ↓ x) ⊴ (Pₒ ↓ y) ↔ pr₁ x ⊴ pr₁ y)
 ↓-⊴-iff-⊴ x y = forward , backward
  where
   forward : (Pₒ ↓ x) ⊴ (Pₒ ↓ y) → pr₁ x ⊴ pr₁ y
   forward h
    = ≼-gives-⊴ x y
       (initial-segments-⊴-gives-simulations-pointwise-≼
         Pₒ Pₒ Pₒ (⊴-refl Pₒ) (⊴-refl Pₒ) x y h)

   backward : pr₁ x ⊴ pr₁ y → (Pₒ ↓ x) ⊴ (Pₒ ↓ y)
   backward h
    = simulations-pointwise-≼-gives-initial-segments-⊴
       Pₒ Pₒ Pₒ (⊴-refl Pₒ) (⊴-refl Pₒ) x y (⊴-gives-≼ x y h)

\end{code}

■ The direct successor construction

For any A, we take the ordinals satisfying P and weakly below A, ordered by
strict ordinal comparison.  This construction lives in the next universe;
it does not assert that the resulting ordinal itself satisfies P.

\begin{code}

 direct-succ : Ordinal 𝓤 → Ordinal (𝓤 ⁺)
 direct-succ A = X , _≺_ , p , w , e , t
  where
   X : 𝓤 ⁺ ̇
   X = Σ C ꞉ Ordinal 𝓤 , P C × (C ⊴ A)

   Y : 𝓤 ⁺ ̇
   Y = Σ a ꞉ ⟨ A ⟩ , P (A ↓ a)

   Q : Ordinal 𝓤 → 𝓤 ⁺ ̇
   Q C = P C × (C ⊴ A)

   Q-is-prop : (C : Ordinal 𝓤) → is-prop (Q C)
   Q-is-prop C = ×-is-prop (P-is-prop C) (⊴-is-prop-valued C A)

   below : (C D : Ordinal 𝓤) → Q D → C ⊲ D → Q C
   below C D (q , h) k
    = P-is-hereditary D C q k ,
      ⊴-trans C D A (⊲-gives-⊴ C D k) h

   _≺_ : X → X → 𝓤 ⁺ ̇
   _≺_ = subtype-order (OO 𝓤) Q

   p : is-prop-valued _≺_
   p = subtype-order-is-prop-valued (OO 𝓤) Q

   w : is-well-founded _≺_
   w = subtype-order-is-well-founded (OO 𝓤) Q

   e : is-extensional _≺_
   e (C , h) (D , k) f g
    = to-subtype-＝ Q-is-prop
       (⊲-is-extensional C D
         (λ E l → f (E , below E C h l) l)
         (λ E l → g (E , below E D k l) l))

   t : is-transitive _≺_
   t = subtype-order-is-transitive (OO 𝓤) Q

\end{code}
