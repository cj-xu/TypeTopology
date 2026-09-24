Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
23 September 2026

We study strong and exact successors within an ordinal, and the thin and
fat successor constructions on ordinals.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.Successors (ua : Univalence) where

open import MLTT.Spartan
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Propositions ua
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.Subsingletons
open import UF.UA-FunExt
open import Ordinals.Arithmetic (Univalence-gives-FunExt ua)
open import Ordinals.LimitPoints (Univalence-gives-FunExt ua)
 using (is-successor-of)
open import Ordinals.WellOrderTransport

private
 ⊲⁻-is-well-order : is-well-order {𝓤 ⁺} {𝓤} _⊲⁻_
 ⊲⁻-is-well-order {𝓤}
  = order-transfer-lemma₃.well-order→ (Univalence-gives-FunExt ua)
     (Ordinal 𝓤) _⊲_ _⊲⁻_ ⊲-is-equivalent-to-⊲⁻ ⊲-is-well-order

\end{code}

■ Strong and exact successors inside a given ordinal B

\begin{code}

module Successors {𝓤 : Universe} (B : Ordinal 𝓤) where

 private
  _≺ᴮ_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
  x ≺ᴮ y = x ≺⟨ B ⟩ y

  _≼ᴮ_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
  x ≼ᴮ y = x ≼⟨ B ⟩ y

\end{code}

A strong successor s of x is a successor which is also weakly below every
strict upper bound of x.

\begin{code}

 _is-strong-succ-of_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
 x is-strong-succ-of y = y ≺ᴮ x
                       × ((z : ⟨ B ⟩) → z ≺ᴮ x → z ≼ᴮ y)
                       × ((z : ⟨ B ⟩) → y ≺ᴮ z → x ≼ᴮ z)

 strong-succ-gives-succ : (s x : ⟨ B ⟩)
                        → s is-strong-succ-of x → is-successor-of B s x
 strong-succ-gives-succ s x strong = pr₁ strong , pr₁ (pr₂ strong)

 calc-strong-succ : (⟨ B ⟩ → ⟨ B ⟩) → 𝓤 ̇
 calc-strong-succ s = (x : ⟨ B ⟩) → (s x) is-strong-succ-of x

\end{code}

An exact successor s of x has as its strict predecessors exactly the elements
weakly below x.  It is a successor in the sense that x is strictly below s,
and every strict predecessor of s is weakly below x.  Exactness additionally
requires every element weakly below x to be strictly below s.

\begin{code}

 _is-exact-succ-of_ : ⟨ B ⟩ → ⟨ B ⟩ → 𝓤 ̇
 s is-exact-succ-of x = (z : ⟨ B ⟩) → (z ≺ᴮ s ↔ z ≼ᴮ x)

 exact-succ-gives-succ : (s x : ⟨ B ⟩)
                       → s is-exact-succ-of x → is-successor-of B s x
 exact-succ-gives-succ s x exact
  = pr₂ (exact x) (Reflexivity B) , (λ z → pr₁ (exact z))

 Has-exact-successors : 𝓤 ̇
 Has-exact-successors = (x : ⟨ B ⟩) → Σ s ꞉ ⟨ B ⟩ , s is-exact-succ-of x

\end{code}

Under mixed transitivity, that is, x ≼ᴮ y → y ≺ᴮ z → x ≺ᴮ z, exact successors
and strong successors coincide.

Without that assumption, we keep the two notions distinct.

\begin{code}

 exact-succ-gives-strong-succ
  : ((x y z : ⟨ B ⟩) → x ≼ᴮ y → y ≺ᴮ z → x ≺ᴮ z)
  → (s x : ⟨ B ⟩)
  → s is-exact-succ-of x → s is-strong-succ-of x
 exact-succ-gives-strong-succ mixed s x exact
  = pr₂ (exact x) (Reflexivity B) ,
    (λ z → pr₁ (exact z)) ,
    (λ y h z k → mixed z x y (pr₁ (exact z) k) h)

 strong-succ-gives-exact-succ
  : ((x y z : ⟨ B ⟩) → x ≼ᴮ y → y ≺ᴮ z → x ≺ᴮ z)
  → (s x : ⟨ B ⟩)
  → s is-strong-succ-of x → s is-exact-succ-of x
 strong-succ-gives-exact-succ mixed s x strong z
  = pr₁ (pr₂ strong) z , (λ h → mixed z x s h (pr₁ strong))

 exact-succ-iff-strong-succ
  : ((x y z : ⟨ B ⟩) → x ≼ᴮ y → y ≺ᴮ z → x ≺ᴮ z)
  → (s x : ⟨ B ⟩)
  → (s is-exact-succ-of x ↔ s is-strong-succ-of x)
 exact-succ-iff-strong-succ mixed s x
  = exact-succ-gives-strong-succ mixed s x ,
    strong-succ-gives-exact-succ mixed s x

\end{code}

■ Thin and fat successors

Following Taylor, we call the following two constructions the thin and fat
successors.  The thin successor adds a new greatest element to A.  The fat
successor consists of all ordinals weakly below A, ordered by strict ordinal
comparison.  Classically these constructions are order-isomorphic, but they
need not coincide constructively.

These constructions apply to any ordinal A. The thin successor stays in
the universe of A; the fat successor as defined here lives in the next
universe, since its elements range over Ordinal 𝓤.

\begin{code}

thin-succ : Ordinal 𝓤 → Ordinal 𝓤
thin-succ A = A +ₒ 𝟙ₒ

fat-succ : Ordinal 𝓤 → Ordinal (𝓤 ⁺)
fat-succ {𝓤} A = X , _≺_ , p , w , e , t
 where
  X : 𝓤 ⁺ ̇
  X = Σ C ꞉ Ordinal 𝓤 , C ⊴ A

  _≺_ : X → X → 𝓤 ⁺ ̇
  (C , _) ≺ (D , _) = C ⊲ D

  p : is-prop-valued _≺_
  p (C , _) (D , _) = ⊲-is-prop-valued C D

  w : is-well-founded _≺_
  w (C , h) = f C (⊲-is-well-founded C) h
   where
    f : (C : Ordinal 𝓤) → is-accessible _⊲_ C
      → (h : C ⊴ A) → is-accessible _≺_ (C , h)
    f C (acc g) h = acc (λ σ l → f (pr₁ σ) (g (pr₁ σ) l) (pr₂ σ))

  below : (C D : Ordinal 𝓤) → C ⊲ D → D ⊴ A → C ⊴ A
  below C D h k = ⊴-trans C D A (⊲-gives-⊴ C D h) k

  e : is-extensional _≺_
  e (C , h) (D , k) f g
   = to-subtype-＝ (λ E → ⊴-is-prop-valued E A)
      (⊲-is-extensional C D
        (λ E l → f (E , below E C l h) l)
        (λ E l → g (E , below E D l k) l))

  t : is-transitive _≺_
  t (C , _) (D , _) (E , _) = ⊲-is-transitive C D E

\end{code}

■ The thin successor is weakly below the fat successor

The canonical simulation sends each element to its initial segment and the
new greatest element to A itself.

\begin{code}

thin-succ-⊴-fat-succ : (A : Ordinal 𝓤) → thin-succ A ⊴ fat-succ A
thin-succ-⊴-fat-succ A = f , i , p
 where
  f : ⟨ thin-succ A ⟩ → ⟨ fat-succ A ⟩
  f (inl a) = (A ↓ a) , segment-⊴ A a
  f (inr ⋆) = A , ⊴-refl A

  i : is-initial-segment (thin-succ A) (fat-succ A) f
  i (inl a) (C , k) ((c , l) , e)
   = inl c , l ,
     to-subtype-＝ (λ D → ⊴-is-prop-valued D A)
      ((e ∙ iterated-↓ A a c l) ⁻¹)
  i (inr ⋆) (C , k) (c , e)
   = inl c , ⋆ , to-subtype-＝ (λ D → ⊴-is-prop-valued D A) (e ⁻¹)

  p : is-order-preserving (thin-succ A) (fat-succ A) f
  p (inl a) (inl b) l = ↓-preserves-order A a b l
  p (inl a) (inr ⋆) l = a , refl
  p (inr ⋆) (inl b) l = 𝟘-elim l
  p (inr ⋆) (inr ⋆) l = 𝟘-elim l

\end{code}

■ The reverse comparison characterizes excluded middle

Excluded middle in the universe of A makes every ordinal weakly below A
an initial segment of A or A itself.  Thus the canonical simulation is an
order equivalence, giving the reverse comparison across universes.

\begin{code}

EM-gives-fat-succ-⊴-thin-succ
 : EM 𝓤 → (A : Ordinal 𝓤) → fat-succ A ⊴ thin-succ A
EM-gives-fat-succ-⊴-thin-succ {𝓤} em A
 = ≃ₒ-to-⊴ (fat-succ A) (thin-succ A)
    (≃ₒ-sym (thin-succ A) (fat-succ A) (f , pr₂ sim , e , r))
 where
  f = pr₁ (thin-succ-⊴-fat-succ A)
  sim = pr₂ (thin-succ-⊴-fat-succ A)

  section : (v : ⟨ fat-succ A ⟩)
          → Σ u ꞉ ⟨ thin-succ A ⟩ , f u ＝ v
  section (C , h) = dispatch (trichotomy₃ _⊲⁻_ em ⊲⁻-is-well-order C A)
   where
    dispatch : (C ⊲⁻ A) + (C ＝ A) + (A ⊲⁻ C)
          → Σ u ꞉ ⟨ thin-succ A ⟩ , f u ＝ (C , h)
    dispatch (inl l)
     = inl (pr₁ k) ,
       to-subtype-＝ (λ D → ⊴-is-prop-valued D A) (pr₂ k ⁻¹)
     where
      k : C ⊲ A
      k = ⌜ ⊲-is-equivalent-to-⊲⁻ C A ⌝⁻¹ l
    dispatch (inr (inl q))
     = inr ⋆ , to-subtype-＝ (λ D → ⊴-is-prop-valued D A) (q ⁻¹)
    dispatch (inr (inr l))
     = 𝟘-elim (⊴-gives-not-⊲ C A h (⌜ ⊲-is-equivalent-to-⊲⁻ A C ⌝⁻¹ l))

  e : is-equiv f
  e = lc-split-surjections-are-equivs f
       (simulations-are-lc (thin-succ A) (fat-succ A) f sim) section

  r : is-order-preserving (fat-succ A) (thin-succ A) (inverse f e)
  r = order-reflecting-gives-inverse-order-preserving
       (thin-succ A) (fat-succ A) f e
       (simulations-are-order-reflecting (thin-succ A) (fat-succ A) f sim)

\end{code}

For the converse, the reverse comparison at the one-element ordinal
already suffices. Its thin successor has two elements; the position of a
proposition, viewed as an element of its fat successor, decides whether
that proposition holds.

\begin{code}

fat-succ-one-⊴-thin-succ-one-gives-EM
 : fat-succ (𝟙ₒ {𝓤}) ⊴ thin-succ 𝟙ₒ → EM 𝓤
fat-succ-one-⊴-thin-succ-one-gives-EM {𝓤} (g , sim) P isp = decide (g v) refl
 where
  T = thin-succ (𝟙ₒ {𝓤})
  F = fat-succ (𝟙ₒ {𝓤})

  canonical : T ⊴ F
  canonical = thin-succ-⊴-fat-succ 𝟙ₒ

  bottom : ⟨ F ⟩
  bottom = pr₁ canonical (inl ⋆)

  bottom-image : g bottom ＝ inl ⋆
  bottom-image = at-most-one-simulation T T
                  (g ∘ pr₁ canonical) id
                  (pr₂ (⊴-trans T F T canonical (g , sim)))
                  (pr₂ (⊴-refl T)) (inl ⋆)

  v : ⟨ F ⟩
  v = prop-ordinal P isp , prop-ordinal-⊴ isp 𝟙-is-prop (λ _ → ⋆)

  holds-gives-below : P → bottom ≺⟨ F ⟩ v
  holds-gives-below p = p , (𝟙ₒ-↓ ∙ (prop-ordinal-↓ isp p ⁻¹))

  decide : (t : ⟨ T ⟩) → g v ＝ t → P + ¬ P
  decide (inl ⋆) q = inr does-not-hold
   where
    does-not-hold : ¬ P
    does-not-hold p
     = 𝟘-elim (transport (λ y → inl ⋆ ≺⟨ T ⟩ y) q
        (transport (λ x → x ≺⟨ T ⟩ g v) bottom-image
          (pr₂ sim bottom v (holds-gives-below p))))
  decide (inr ⋆) q = inl (pr₁ below)
   where
    images-below : g bottom ≺⟨ T ⟩ g v
    images-below
     = transport (λ y → g bottom ≺⟨ T ⟩ y) (q ⁻¹)
        (transport (λ x → x ≺⟨ T ⟩ inr ⋆) (bottom-image ⁻¹) ⋆)

    below : bottom ≺⟨ F ⟩ v
    below = simulations-are-order-reflecting F T g sim bottom v images-below

fat-succ-⊴-thin-succ-gives-EM
 : ((A : Ordinal 𝓤) → fat-succ A ⊴ thin-succ A) → EM 𝓤
fat-succ-⊴-thin-succ-gives-EM h
 = fat-succ-one-⊴-thin-succ-one-gives-EM (h 𝟙ₒ)

fat-succ-⊴-thin-succ-iff-EM
 : ((A : Ordinal 𝓤) → fat-succ A ⊴ thin-succ A) ↔ EM 𝓤
fat-succ-⊴-thin-succ-iff-EM
 = fat-succ-⊴-thin-succ-gives-EM , EM-gives-fat-succ-⊴-thin-succ

\end{code}

We now study the properties of thin and fat successors.

\begin{code}

module _ {𝓤 : Universe} where

 open Successors (OO 𝓤)

\end{code}

■ Thin successors are strong, but need not be exact constructively

The thin successor is a successor of A in the ordinal of ordinals.  It is
also strong: it is weakly below every ordinal strictly above A.

\begin{code}

 thin-succ-is-succ : (A : Ordinal 𝓤)
                   → is-successor-of (OO 𝓤) (thin-succ A) A
 thin-succ-is-succ A = successor-increasing A , below
  where
   below : (C : Ordinal _) → C ⊲ thin-succ A → C ≼ A
   below C (inl a , refl)
    = ⊴-gives-≼ _ A (successor-lemma-left A a)
   below C (inr ⋆ , refl)
    = ⊴-gives-≼ _ A (＝-to-⊴ _ A (successor-lemma-right A))

 thin-succ-is-strong-succ : (A : Ordinal 𝓤)
                          → (thin-succ A) is-strong-succ-of A
 thin-succ-is-strong-succ A
  = pr₁ (thin-succ-is-succ A) , pr₂ (thin-succ-is-succ A) , least
  where
   least : (C : Ordinal _) → A ⊲ C → thin-succ A ≼ C
   least C (c , refl)
    = ⊴-gives-≼ _ C (upper-bound-of-successors-of-initial-segments C c)

\end{code}

However, the thin successor need not be exact constructively.

Already exactness at the one-element ordinal implies excluded middle:
a proposition is weakly below that ordinal, whereas being strictly below
its thin successor forces it to be empty or inhabited.

\begin{code}

 thin-succ-one-is-exact-succ-gives-EM
  : thin-succ 𝟙ₒ is-exact-succ-of 𝟙ₒ → EM 𝓤
 thin-succ-one-is-exact-succ-gives-EM exact P isp = decide below
  where
   C : Ordinal 𝓤
   C = prop-ordinal P isp

   below : C ⊲ thin-succ 𝟙ₒ
   below = pr₂ (exact C)
            (⊴-gives-≼ C 𝟙ₒ (prop-ordinal-⊴ isp 𝟙-is-prop (λ _ → ⋆)))

   decide : C ⊲ thin-succ 𝟙ₒ → P + ¬ P
   decide (inl ⋆ , e) = inr does-not-hold
    where
     does-not-hold : ¬ P
     does-not-hold p = empty (transport ⟨_⟩ e p)
      where
       empty : ⟨ thin-succ (𝟙ₒ {𝓤}) ↓ inl ⋆ ⟩ → 𝟘
       empty (inl ⋆ , l) = 𝟘-elim l
       empty (inr ⋆ , l) = 𝟘-elim l
   decide (inr ⋆ , e) = inl (transport⁻¹ ⟨_⟩ e (inl ⋆ , ⋆))

 thin-succ-is-exact-succ-gives-EM
  : ((A : Ordinal 𝓤) → (thin-succ A) is-exact-succ-of A) → EM 𝓤
 thin-succ-is-exact-succ-gives-EM exact
  = thin-succ-one-is-exact-succ-gives-EM (exact 𝟙ₒ)

\end{code}

For the converse, excluded middle gives trichotomy for ordinal comparison.
If C is weakly below A, then either C is strictly below A or C equals A;
both cases put C strictly below the thin successor of A.  We use the small
comparison ⊲⁻ so that excluded middle in 𝓤 suffices.

\begin{code}

 EM-gives-thin-succ-is-exact-succ
  : EM 𝓤 → (A : Ordinal 𝓤) → (thin-succ A) is-exact-succ-of A
 EM-gives-thin-succ-is-exact-succ em A C
  = pr₂ (thin-succ-is-succ A) C , backward
  where
   backward : C ≼ A → C ⊲ thin-succ A
   backward h = dispatch (trichotomy₃ _⊲⁻_ em ⊲⁻-is-well-order C A)
    where
     dispatch : (C ⊲⁻ A) + (C ＝ A) + (A ⊲⁻ C) → C ⊲ thin-succ A
     dispatch (inl l)
      = ⊲-is-transitive C A (thin-succ A)
         (⌜ ⊲-is-equivalent-to-⊲⁻ C A ⌝⁻¹ l) (successor-increasing A)
     dispatch (inr (inl e))
      = transport⁻¹ (_⊲ thin-succ A) e (successor-increasing A)
     dispatch (inr (inr l))
      = 𝟘-elim (⊴-gives-not-⊲ C A (≼-gives-⊴ C A h)
                 (⌜ ⊲-is-equivalent-to-⊲⁻ A C ⌝⁻¹ l))

 thin-succ-is-exact-succ-iff-EM
  : ((A : Ordinal 𝓤) → (thin-succ A) is-exact-succ-of A) ↔ EM 𝓤
 thin-succ-is-exact-succ-iff-EM
  = thin-succ-is-exact-succ-gives-EM , EM-gives-thin-succ-is-exact-succ

\end{code}

■ Fat successors are exact, but need not be strong constructively

For the fat successor we use the cross-universe comparison ⊲⁻, since it
lives one universe higher.  Its initial segment at (C , h) is order-isomorphic
to C.  Consequently, its predecessors from the universe of A are exactly
the ordinals weakly below A. Therefore, fat successors are exact.

\begin{code}

fat-succ-initial-segment : (A C : Ordinal 𝓤) (h : C ⊴ A)
                         → C ≃ₒ (fat-succ A ↓ (C , h))
fat-succ-initial-segment {𝓤} A C h
 = transport⁻¹ (C ≃ₒ_) q (ordinals-in-OO-are-lowersets-of-OO C)
 where
  inclusion : fat-succ A ⊴ OO 𝓤
  inclusion = pr₁ , i , (λ _ _ → id)
   where
    i : is-initial-segment (fat-succ A) (OO 𝓤) pr₁
    i (D , k) E l
     = (E , ⊴-trans E D A (⊲-gives-⊴ E D l) k) , l , refl

  q : (fat-succ A ↓ (C , h)) ＝ (OO 𝓤 ↓ C)
  q = simulations-preserve-↓ (fat-succ A) (OO 𝓤) inclusion (C , h)

fat-succ-is-exact-succ : (A C : Ordinal 𝓤)
                       → (C ⊲⁻ fat-succ A ↔ C ⊴ A)
fat-succ-is-exact-succ A C = forward , backward
 where
  forward : C ⊲⁻ fat-succ A → C ⊴ A
  forward ((D , h) , e)
   = ⊴-trans C D A
      (≃ₒ-to-⊴ C D
        (≃ₒ-trans C _ D e
          (≃ₒ-sym D _ (fat-succ-initial-segment A D h)))) h

  backward : C ⊴ A → C ⊲⁻ fat-succ A
  backward h = (C , h) , fat-succ-initial-segment A C h

\end{code}

We have already proved the successor property for fat-succ. The additional
clause for strongness would say that fat-succ A is weakly below every
ordinal strictly above A.  Even restricting those upper bounds to the
universe of A, this clause at the one-element ordinal implies excluded
middle: take its thin successor as the strict upper bound.

We call this clause relative leastness, with upper bounds restricted to the
input universe. It is the additional clause for strongness, rather than the
full internal successor predicate defined above.

\begin{code}

Fat-succ-relative-leastness : Ordinal 𝓤 → 𝓤 ⁺ ̇
Fat-succ-relative-leastness {𝓤} A = (C : Ordinal 𝓤) → A ⊲ C → fat-succ A ⊴ C

fat-succ-one-relative-leastness-gives-EM
 : Fat-succ-relative-leastness (𝟙ₒ {𝓤}) → EM 𝓤
fat-succ-one-relative-leastness-gives-EM least
 = fat-succ-one-⊴-thin-succ-one-gives-EM
    (least (thin-succ 𝟙ₒ) (successor-increasing 𝟙ₒ))

fat-succ-relative-leastness-gives-EM
 : ((A : Ordinal 𝓤) → Fat-succ-relative-leastness A) → EM 𝓤
fat-succ-relative-leastness-gives-EM least
 = fat-succ-one-relative-leastness-gives-EM (least 𝟙ₒ)

EM-gives-fat-succ-relative-leastness
 : EM 𝓤 → (A : Ordinal 𝓤) → Fat-succ-relative-leastness A
EM-gives-fat-succ-relative-leastness em A C (c , refl)
 = ⊴-trans (fat-succ (C ↓ c)) (thin-succ (C ↓ c)) C
    (EM-gives-fat-succ-⊴-thin-succ em (C ↓ c))
    (upper-bound-of-successors-of-initial-segments C c)

fat-succ-relative-leastness-iff-EM
 : ((A : Ordinal 𝓤) → Fat-succ-relative-leastness A) ↔ EM 𝓤
fat-succ-relative-leastness-iff-EM
 = fat-succ-relative-leastness-gives-EM , EM-gives-fat-succ-relative-leastness

\end{code}
