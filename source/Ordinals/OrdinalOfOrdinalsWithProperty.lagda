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
open import Ordinals.InducedSuccessor ua
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
 hiding (⊴-gives-≼)
 renaming (≼-gives-⊴ to ordinal-≼-gives-⊴)
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.SmallWeakPredecessors ua
open import UF.Subsingletons
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets-Properties
open import UF.Size
open import UF.UA-FunExt
 using (Univalence-gives-FunExt; Univalence-gives-Fun-Ext)
open import Ordinals.WellOrderTransport (Univalence-gives-FunExt ua)

module WithProperty
        {𝓤 : Universe}
        (P : Ordinal 𝓤 → 𝓤 ⁺ ̇ )
        (P-is-prop : (A : Ordinal 𝓤) → is-prop (P A))
        (P-is-hereditary : (A C : Ordinal 𝓤) → P A → C ⊲ A → P C)
       where

 Ordinals-with-property : 𝓤 ⁺ ̇
 Ordinals-with-property = Σ A ꞉ Ordinal 𝓤 , P A

 property-order
  : Ordinals-with-property → Ordinals-with-property → 𝓤 ⁺ ̇
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

Comparison of predecessors within Pₒ is equivalent to comparison of all
ordinal predecessors.

\begin{code}

 ≼-gives-⊴
  : (x y : ⟨ Pₒ ⟩) → x ≼⟨ Pₒ ⟩ y → pr₁ x ⊴ pr₁ y
 ≼-gives-⊴ (A , p) (B , q) h
  = ordinal-≼-gives-⊴ A B (λ C k → h (C , P-is-hereditary A C p k) k)

 ⊴-gives-≼
  : (x y : ⟨ Pₒ ⟩) → pr₁ x ⊴ pr₁ y → x ≼⟨ Pₒ ⟩ y
 ⊴-gives-≼ (A , p) (B , q) h (C , r) k = ⊲-⊴-gives-⊲ C A B k h

 ≼-iff-⊴
  : (x y : ⟨ Pₒ ⟩) → (x ≼⟨ Pₒ ⟩ y ↔ pr₁ x ⊴ pr₁ y)
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

■ Restricting the fat successor by the property

For any A, we restrict its fat successor to the ordinals satisfying P.  Thus,
its elements are the ordinals satisfying P and weakly below A, ordered by
strict ordinal comparison.  This construction lives in the next universe.

\begin{code}

 restricted-fat-succ : Ordinal 𝓤 → Ordinal (𝓤 ⁺)
 restricted-fat-succ A = X , _≺_ , p , w , e , t
  where
   X : 𝓤 ⁺ ̇
   X = Σ C ꞉ Ordinal 𝓤 , P C × C ⊴ A

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

Every initial segment of the restricted fat successor represents the ordinal
indexing its endpoint.  The canonical map to OO preserves these segments.

\begin{code}

 restricted-fat-succ-⊴-OO
  : (A : Ordinal 𝓤) → restricted-fat-succ A ⊴ OO 𝓤
 restricted-fat-succ-⊴-OO A = pr₁ , initial , (λ x y l → l)
  where
   initial : is-initial-segment (restricted-fat-succ A) (OO 𝓤) pr₁
   initial (C , p , h) D l
    = (D , P-is-hereditary C D p l ,
           ⊴-trans D C A (⊲-gives-⊴ D C l) h) , l , refl

 restricted-fat-succ-initial-segment
  : (A C : Ordinal 𝓤) (p : P C) (h : C ⊴ A)
  → C ≃ₒ (restricted-fat-succ A ↓ (C , p , h))
 restricted-fat-succ-initial-segment A C p h
  = ≃ₒ-trans C (OO 𝓤 ↓ C) (restricted-fat-succ A ↓ (C , p , h))
     (ordinals-in-OO-are-lowersets-of-OO C)
     (simulations-pointwise-equal-gives-isomorphic-initial-segments
       (OO 𝓤) (restricted-fat-succ A) (OO 𝓤)
       (⊴-refl (OO 𝓤)) (restricted-fat-succ-⊴-OO A)
       C (C , p , h) refl)

\end{code}

■ Agreement with the induced successor

If A satisfies P, its initial segment in Pₒ represents A.  The restricted
fat successor of A therefore coincides with the successor of this initial
segment induced by Pₒ.

\begin{code}

 open InducedSuccessor Pₒ using (induced-succ)

 restricted-fat-succ-equals-induced-succ
  : (A : Ordinal 𝓤) (p : P A)
  → restricted-fat-succ A ＝ induced-succ (Pₒ ↓ (A , p))
 restricted-fat-succ-equals-induced-succ A p
  = ⊴-antisym D I forward backward
  where
   D = restricted-fat-succ A
   I = induced-succ (Pₒ ↓ (A , p))

   f : ⟨ D ⟩ → ⟨ I ⟩
   f (C , q , h) = (C , q) , pr₂ (↓-⊴-iff-⊴ (C , q) (A , p)) h

   g : ⟨ I ⟩ → ⟨ D ⟩
   g ((C , q) , h) = C , q , pr₁ (↓-⊴-iff-⊴ (C , q) (A , p)) h

   fg : (y : ⟨ I ⟩) → f (g y) ＝ y
   fg y
    = to-subtype-＝
       (λ x → ⊴-is-prop-valued (Pₒ ↓ x) (Pₒ ↓ (A , p))) refl

   gf : (x : ⟨ D ⟩) → g (f x) ＝ x
   gf x
    = to-subtype-＝
       (λ C → ×-is-prop (P-is-prop C) (⊴-is-prop-valued C A)) refl

   forward : D ⊴ I
   forward = f , (λ x y l → g y , l , fg y) , (λ x y l → l)

   backward : I ⊴ D
   backward = g , (λ x y l → f y , l , gf y) , (λ x y l → l)

\end{code}

■ A small version of the restricted fat successor

A chosen small representative of the weak predecessors of each ordinal lets
us restrict them by P.  We resize the strict order and transfer the ordinal
structure along the resulting carrier equivalence.

\begin{code}

module WithPropertyAndResizing
        {𝓤 : Universe}
        (P : Ordinal 𝓤 → 𝓤 ⁺ ̇ )
        (P-is-prop : (A : Ordinal 𝓤) → is-prop (P A))
        (P-is-hereditary : (A C : Ordinal 𝓤) → P A → C ⊲ A → P C)
        (ρ : propositional-resizing (𝓤 ⁺) 𝓤)
        (weak-predecessors-are-small : Weak-predecessors-are-small)
       where

 open WithProperty P P-is-prop P-is-hereditary public

 private
  module Construction (A : Ordinal 𝓤) where

   Small-weak-predecessors : 𝓤 ̇
   Small-weak-predecessors
    = resized (Weak-predecessors A) (weak-predecessors-are-small A)

   weak-predecessor-equiv
    : Small-weak-predecessors ≃ Weak-predecessors A
   weak-predecessor-equiv
    = resizing-condition (weak-predecessors-are-small A)

   represented-ordinal : Small-weak-predecessors → Ordinal 𝓤
   represented-ordinal w = pr₁ (⌜ weak-predecessor-equiv ⌝ w)

   Q : Small-weak-predecessors → 𝓤 ̇
   Q w = resize ρ (P (represented-ordinal w)) (P-is-prop _)

   Carrier : 𝓤 ̇
   Carrier = Σ w ꞉ Small-weak-predecessors , Q w

   Q-equiv-P
    : (w : Small-weak-predecessors) → Q w ≃ P (represented-ordinal w)
   Q-equiv-P w
    = resizing-condition (ρ (P (represented-ordinal w)) (P-is-prop _))

   carrier-equiv : Carrier ≃ ⟨ restricted-fat-succ A ⟩
   carrier-equiv =
     (Σ w ꞉ Small-weak-predecessors , Q w)
      ≃⟨ Σ-cong Q-equiv-P ⟩
     (Σ w ꞉ Small-weak-predecessors , P (represented-ordinal w))
      ≃⟨ Σ-change-of-variable-≃
          (P ∘ pr₁) weak-predecessor-equiv ⟩
     (Σ w ꞉ Weak-predecessors A , P (pr₁ w))
      ≃⟨ Σ-assoc ⟩
     (Σ C ꞉ Ordinal 𝓤 , C ⊴ A × P C)
      ≃⟨ Σ-cong (λ _ → ×-comm) ⟩
     (Σ C ꞉ Ordinal 𝓤 , P C × C ⊴ A)
     ■

   small-order : resizable-order (restricted-fat-succ A) 𝓤
   small-order
    = (λ x y → resize ρ (x ≺⟨ restricted-fat-succ A ⟩ y)
                        (Prop-valuedness (restricted-fat-succ A) x y)) ,
      (λ x y → ≃-sym (resizing-condition
       (ρ (x ≺⟨ restricted-fat-succ A ⟩ y)
        (Prop-valuedness (restricted-fat-succ A) x y))))

   small-structure
    : Σ s ꞉ OrdinalStructure Carrier ,
       (Carrier , s) ≃ₒ restricted-fat-succ A
   small-structure
    = transfer-structure Carrier (restricted-fat-succ A)
       carrier-equiv small-order

 restricted-fat-succ-small : Ordinal 𝓤 → Ordinal 𝓤
 restricted-fat-succ-small A
  = Construction.Carrier A , pr₁ (Construction.small-structure A)

 restricted-fat-succ-small-≃ₒ-restricted-fat-succ
  : (A : Ordinal 𝓤)
  → restricted-fat-succ-small A ≃ₒ restricted-fat-succ A
 restricted-fat-succ-small-≃ₒ-restricted-fat-succ A
  = pr₂ (Construction.small-structure A)

 private
  small-to-large
   : (A : Ordinal 𝓤)
   → ⟨ restricted-fat-succ-small A ⟩ → ⟨ restricted-fat-succ A ⟩
  small-to-large A
   = ≃ₒ-to-fun (restricted-fat-succ-small A) (restricted-fat-succ A)
      (restricted-fat-succ-small-≃ₒ-restricted-fat-succ A)

  large-to-small
   : (A : Ordinal 𝓤)
   → ⟨ restricted-fat-succ A ⟩ → ⟨ restricted-fat-succ-small A ⟩
  large-to-small A
   = ≃ₒ-to-fun⁻¹ (restricted-fat-succ-small A) (restricted-fat-succ A)
      (restricted-fat-succ-small-≃ₒ-restricted-fat-succ A)

  small-to-large-after-large-to-small
   : (A : Ordinal 𝓤) (y : ⟨ restricted-fat-succ A ⟩)
   → small-to-large A (large-to-small A y) ＝ y
  small-to-large-after-large-to-small A
   = ≃-sym-is-rinv
      (≃ₒ-gives-≃
        (restricted-fat-succ-small A)
        (restricted-fat-succ A)
        (restricted-fat-succ-small-≃ₒ-restricted-fat-succ A))

  small-segment-equality
   : (A : Ordinal 𝓤) (x : ⟨ restricted-fat-succ-small A ⟩)
   → (restricted-fat-succ-small A ↓ x) ＝ pr₁ (small-to-large A x)
  small-segment-equality A x
   = eqtoidₒ (ua 𝓤) (Univalence-gives-Fun-Ext ua) (S ↓ x) C
      (≃ₒ-trans (S ↓ x) (L ↓ f x) C segment-equiv
        (≃ₒ-sym C (L ↓ f x)
          (restricted-fat-succ-initial-segment A C p h)))
   where
    S = restricted-fat-succ-small A
    L = restricted-fat-succ A
    e = restricted-fat-succ-small-≃ₒ-restricted-fat-succ A
    f = small-to-large A
    C = pr₁ (f x)
    p = pr₁ (pr₂ (f x))
    h = pr₂ (pr₂ (f x))

    segment-equiv : (S ↓ x) ≃ₒ (L ↓ f x)
    segment-equiv
     = simulations-pointwise-equal-gives-isomorphic-initial-segments
        S L L (≃ₒ-to-⊴ S L e) (⊴-refl L) x (f x) refl

 ⊲-restricted-fat-succ-small-gives-P-and-⊴
  : (A C : Ordinal 𝓤)
  → C ⊲ restricted-fat-succ-small A → P C × (C ⊴ A)
 ⊲-restricted-fat-succ-small-gives-P-and-⊴ A C (x , q)
  = transport⁻¹ (λ D → P D × (D ⊴ A))
     (q ∙ small-segment-equality A x) (pr₂ (small-to-large A x))

 P-and-⊴-gives-⊲-restricted-fat-succ-small
  : (A C : Ordinal 𝓤)
  → P C × (C ⊴ A) → C ⊲ restricted-fat-succ-small A
 P-and-⊴-gives-⊲-restricted-fat-succ-small A C (p , h)
  = x ,
    ((small-segment-equality A x
      ∙ ap pr₁ (small-to-large-after-large-to-small A y)) ⁻¹)
  where
   y = C , p , h
   x = large-to-small A y

 restricted-fat-succ-small-predecessors
  : (A C : Ordinal 𝓤)
  → (C ⊲ restricted-fat-succ-small A ↔ P C × (C ⊴ A))
 restricted-fat-succ-small-predecessors A C
  = ⊲-restricted-fat-succ-small-gives-P-and-⊴ A C ,
    P-and-⊴-gives-⊲-restricted-fat-succ-small A C

\end{code}
