# Involutions

```agda
module foundation.involutions where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.negation
open import foundation.structure-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation.postcomposition-functions
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import structured-types.pointed-types
```

</details>

## Idea

An **involution** on a type `A` is a map `f : A → A` such that `(f ∘ f) ~ id`.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  is-involution : (A → A) → UU l
  is-involution f = (f ∘ f) ~ id

  is-involution-aut : Aut A → UU l
  is-involution-aut e = is-involution (map-equiv e)
```

### The type of involutions on `A`

```agda
involution : {l : Level} → UU l → UU l
involution A = Σ (A → A) is-involution

module _
  {l : Level} {A : UU l} (f : involution A)
  where

  map-involution : A → A
  map-involution = pr1 f

  is-involution-map-involution : is-involution map-involution
  is-involution-map-involution = pr2 f
```

## Properties

### Involutions are equivalences

```agda
is-equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} is-involution-f =
  is-equiv-is-invertible f is-involution-f is-involution-f

is-equiv-map-involution :
  {l : Level} {A : UU l} (f : involution A) → is-equiv (map-involution f)
is-equiv-map-involution = is-equiv-is-involution ∘ is-involution-map-involution

equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → A ≃ A
pr1 (equiv-is-involution {f = f} is-involution-f) = f
pr2 (equiv-is-involution is-involution-f) =
  is-equiv-is-involution is-involution-f

equiv-involution :
  {l : Level} {A : UU l} → involution A → A ≃ A
equiv-involution f =
  equiv-is-involution {f = map-involution f} (is-involution-map-involution f)
```

### Involutions are their own inverse

```agda
htpy-own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → map-inv-equiv f ~ map-equiv f
htpy-own-inverse-is-involution {f = f} is-involution-f x =
  is-injective-equiv f
    ( htpy-eq-equiv (right-inverse-law-equiv f) x ∙
      inv (is-involution-f x))

own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → inv-equiv f ＝ f
own-inverse-is-involution {f = f} =
  eq-htpy-equiv ∘ htpy-own-inverse-is-involution {f = f}
```

### Characterizing equality of involutions

```agda
module _
  {l : Level} {A : UU l}
  where

  coherence-htpy-involution :
    (s t : involution A) → map-involution s ~ map-involution t → UU l
  coherence-htpy-involution s t H =
    ( is-involution-map-involution s) ~
    ( horizontal-concat-htpy H H ∙h is-involution-map-involution t)

  htpy-involution : (s t : involution A) → UU l
  htpy-involution s t =
    Σ ( map-involution s ~ map-involution t)
      ( coherence-htpy-involution s t)

  htpy-htpy-involution :
    {s t : involution A} →
    htpy-involution s t → (map-involution s) ~ (map-involution t)
  htpy-htpy-involution = pr1

  coherence-htpy-involution-htpy-involution :
    {s t : involution A} → (H : htpy-involution s t) →
    coherence-htpy-involution s t (htpy-htpy-involution H)
  coherence-htpy-involution-htpy-involution = pr2  

  refl-htpy-involution : (s : involution A) → htpy-involution s s
  pr1 (refl-htpy-involution s) = refl-htpy
  pr2 (refl-htpy-involution s) = refl-htpy

  htpy-eq-involution : (s t : involution A) → s ＝ t → htpy-involution s t
  htpy-eq-involution s .s refl = refl-htpy-involution s

  is-torsorial-htpy-involution :
    (s : involution A) → is-torsorial (htpy-involution s)
  is-torsorial-htpy-involution s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-involution s))
      ( map-involution s , refl-htpy)
      ( is-torsorial-htpy (is-involution-map-involution s))

  is-equiv-htpy-eq-involution :
    (s t : involution A) → is-equiv (htpy-eq-involution s t)
  is-equiv-htpy-eq-involution s =
    fundamental-theorem-id
      ( is-torsorial-htpy-involution s)
      ( htpy-eq-involution s)

  extensionality-involution :
    (s t : involution A) → (s ＝ t) ≃ (htpy-involution s t)
  pr1 (extensionality-involution s t) = htpy-eq-involution s t
  pr2 (extensionality-involution s t) = is-equiv-htpy-eq-involution s t

  eq-htpy-involution : (s t : involution A) → htpy-involution s t → s ＝ t
  eq-htpy-involution s t = map-inv-equiv (extensionality-involution s t)
```

### If `A` is `k`-truncated then the type of involutions is `k`-truncated

```agda
is-trunc-is-involution :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc (succ-𝕋 k) A → (f : A → A) → is-trunc k (is-involution f)
is-trunc-is-involution k is-trunc-A f =
  is-trunc-Π k λ x → is-trunc-A (f (f x)) x

is-involution-Truncated-Type :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc (succ-𝕋 k) A → (A → A) → Truncated-Type l k
pr1 (is-involution-Truncated-Type k is-trunc-A f) = is-involution f
pr2 (is-involution-Truncated-Type k is-trunc-A f) =
  is-trunc-is-involution k is-trunc-A f

is-trunc-involution :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-trunc k A → is-trunc k (involution A)
is-trunc-involution k is-trunc-A =
  is-trunc-Σ
    ( is-trunc-function-type k is-trunc-A)
    ( is-trunc-is-involution k (is-trunc-succ-is-trunc k is-trunc-A))

involution-Truncated-Type :
  {l : Level} (k : 𝕋) → Truncated-Type l k → Truncated-Type l k
pr1 (involution-Truncated-Type k (A , is-trunc-A)) = involution A
pr2 (involution-Truncated-Type k (A , is-trunc-A)) =
  is-trunc-involution k is-trunc-A
```

### Involutions on dependent function types

```agda
involution-Π-involution-fam :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → involution (B x)) → involution ((x : A) → B x)
pr1 (involution-Π-involution-fam i) f x =
  map-involution (i x) (f x)
pr2 (involution-Π-involution-fam i) f =
  eq-htpy (λ x → is-involution-map-involution (i x) (f x))
```

### Coherence of involutions

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : is-involution f)
  where

  coherence-is-involution : UU l
  coherence-is-involution = f ·l H ~ H ·r f
```

### Equivalences act by conjugation on involutions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {X : UU l2} (e : A ≃ X)
  where
  
  conjugate-equiv-involution :
    involution A → involution X
  pr1 (conjugate-equiv-involution f) =
    conjugate-equiv e (map-involution f)
  pr2 (conjugate-equiv-involution f) =
    ( inv-htpy
      ( distributive-conjugate-equiv-comp
        ( e)
        ( map-involution f)
        ( map-involution f))) ∙h
    ( htpy-conjugate-equiv e (is-involution-map-involution f)) ∙h
    ( is-section-map-inv-equiv e)

  htpy-conjugate-equiv-involution :
    {f g : involution A} → htpy-involution f g →
    htpy-involution
      ( conjugate-equiv-involution f)
      ( conjugate-equiv-involution g)
  pr1 (htpy-conjugate-equiv-involution H) =
    htpy-conjugate-equiv e  (htpy-htpy-involution H)
  pr2 (htpy-conjugate-equiv-involution {f} {g} H) =
    {!right-whisker-comp²!}
-- double-whisker-comp (map-equiv e ∘ map-involution f) (is-retraction-map-inv-equiv e) (map-involution f ∘ map-inv-equiv e)
  conjugate-inv-equiv-involution :
    involution X → involution A
  pr1 (conjugate-inv-equiv-involution f) =
    (map-inv-equiv e) ∘ (map-involution f) ∘ (map-equiv e)
  pr2 (conjugate-inv-equiv-involution f) =
    (inv-htpy
      ( distributive-conjugate-inv-equiv-comp
        ( e)
        ( map-involution f)
        ( map-involution f))) ∙h
    ( htpy-conjugate-inv-equiv e (is-involution-map-involution f)) ∙h
    ( is-retraction-map-inv-equiv e)

  htpy-conjugate-inv-equiv-involution :
    {!!}
  htpy-conjugate-inv-equiv-involution = {!!}
```

### The above process preserves ___

```agda
contraction-involution-equiv-contraction-involution :
  {l1 l2 : Level} (A : UU l1) (X : UU l2) (e : A ≃ X) (f : involution A)
  (H : (g : involution A) → htpy-involution f g) →
  (g : involution X) → htpy-involution (conjugate-equiv-involution e f) g
pr1 (contraction-involution-equiv-contraction-involution A X e f H g) =
  {!transpose-conjugate-inv-equiv e (H (conjugate-inv-equiv-involution e g))!} --
pr2 (contraction-involution-equiv-contraction-involution A X e f H g) =
  {!( coherence-htpy-involution-htpy-involution (H (conjugate-inv-equiv-involution A X e g)))!}

{-  ( double-whisker-comp
    ( map-equiv e)
    ( htpy-htpy-involution (H (conjugate-inv-equiv-involution A X e g)))
    ( map-inv-equiv e)) ∙h
  ( right-whisker-comp
    ( is-section-map-inv-equiv e)
    ( map-involution g ∘ map-equiv e ∘ map-inv-equiv e)) ∙h
  ( left-whisker-comp
    ( map-involution g)
    ( is-section-map-inv-equiv e))-}



{-  is-injective-equiv
    ( equiv-precomp e X)
    ( is-injective-equiv
      ( equiv-postcomp A (inv-equiv e))
      ( ( eq-htpy
        ( ( left-whisker-comp (map-inv-equiv e ∘ map-equiv e ∘ map-involution f) (is-retraction-map-inv-equiv e)) ∙h
        ( right-whisker-comp (is-retraction-map-inv-equiv e) (map-involution f)))) ∙
      ( ( H (conjugate-inv-equiv-involution A X e g)))))-}
```
 
### Fixed point free involutions

```agda
module _
  {l : Level}
  where

  is-fixed-point-free-involution :
    {X : UU l} → involution X → UU l 
  is-fixed-point-free-involution {X} =
    (is-fixed-point-free-endomorphism X) ∘ map-involution

  fixed-point-free-involution :
    UU l → UU l
  fixed-point-free-involution X = Σ (involution X) is-fixed-point-free-involution

module _
  {l : Level} {X : UU l}
  where

  involution-fixed-point-free-involution :
    fixed-point-free-involution X → involution X
  involution-fixed-point-free-involution = pr1

  map-fixed-point-free-involution :
    fixed-point-free-involution X → X → X
  map-fixed-point-free-involution =
    map-involution ∘ involution-fixed-point-free-involution

  is-fixed-point-free-involution-fixed-point-free-involution :
    (f : fixed-point-free-involution X) →
    is-fixed-point-free-involution (involution-fixed-point-free-involution f)
  is-fixed-point-free-involution-fixed-point-free-involution = pr2
```

### The subtype of fixed point free involutions

```agda
  is-subtype-is-fixed-point-free-involution :
    is-subtype (is-fixed-point-free-involution {X = X})
  is-subtype-is-fixed-point-free-involution f =
    is-prop-Π λ x → is-prop-neg

  subtype-fixed-point-free-involution :
    subtype l (involution X)
  pr1 (subtype-fixed-point-free-involution f) =
    is-fixed-point-free-involution f
  pr2 (subtype-fixed-point-free-involution f) =
    is-subtype-is-fixed-point-free-involution f
```

### We can obtain a fixed point free involution on a type equivalent to a type equipped with a fixed point free involution

```agda
fixed-point-free-involution-equiv-fixed-point-free-involution :
  {l1 l2 : Level} (A : UU l1) (X : UU l2) (e :  A ≃ X) → fixed-point-free-involution A → fixed-point-free-involution X
pr1 (fixed-point-free-involution-equiv-fixed-point-free-involution A X e f) =
  conjugate-equiv-involution e (involution-fixed-point-free-involution f)
pr2 (fixed-point-free-involution-equiv-fixed-point-free-involution A X e f) x t =
  is-fixed-point-free-involution-fixed-point-free-involution
    ( f)
    ( map-inv-equiv e x)
    ( is-injective-equiv e (t ∙ inv (is-section-map-inv-equiv e x)))

fixed-point-free-involution-equiv-fixed-point-free-involution' : 
    {l1 l2 : Level} (A : UU l1) (X : UU l2) (e :  A ≃ X) → fixed-point-free-involution X → fixed-point-free-involution A
pr1 (fixed-point-free-involution-equiv-fixed-point-free-involution' A X e f) = 
  conjugate-inv-equiv-involution e (involution-fixed-point-free-involution f)
pr2 (fixed-point-free-involution-equiv-fixed-point-free-involution' A X e f) x t =
  is-fixed-point-free-involution-fixed-point-free-involution
    ( f)
    ( map-equiv e x)
    ( is-injective-equiv (inv-equiv e) (t ∙ inv (is-retraction-map-inv-equiv e x)))
```

```agda
contraction-fixed-point-free-involution-equiv-contraction-fixed-point-free-involution :
  {l1 l2 : Level} (A : UU l1) (X : UU l2) (e : A ≃ X) (f : fixed-point-free-involution A)
  (H : (g : fixed-point-free-involution A) →
  (map-fixed-point-free-involution f) ＝ (map-fixed-point-free-involution g)) →
  (g : fixed-point-free-involution X) →
  ( ( map-fixed-point-free-involution (fixed-point-free-involution-equiv-fixed-point-free-involution A X e f)) ＝
  ( map-fixed-point-free-involution g))
contraction-fixed-point-free-involution-equiv-contraction-fixed-point-free-involution A X e f H g =
  is-injective-equiv
    ( equiv-precomp e X)
    ( is-injective-equiv
      ( equiv-postcomp A (inv-equiv e))
      ( ( eq-htpy
        ( ( left-whisker-comp
          ( map-inv-equiv e ∘ map-equiv e ∘ map-fixed-point-free-involution f)
          ( is-retraction-map-inv-equiv e)) ∙h
        ( right-whisker-comp
          ( is-retraction-map-inv-equiv e)
          ( map-fixed-point-free-involution f)))) ∙
      ( ( H (fixed-point-free-involution-equiv-fixed-point-free-involution' A X e g)))))

is-contr-fixed-point-free-involution-equiv-is-contr-fixed-point-free-involution :
  {l1 l2 : Level} (A : UU l1) (X : UU l2) (e : A ≃ X) (f : fixed-point-free-involution A) →
  is-contr (fixed-point-free-involution A) → is-contr (fixed-point-free-involution X)
pr1 (is-contr-fixed-point-free-involution-equiv-is-contr-fixed-point-free-involution A X e f t) = {!!}
pr2 (is-contr-fixed-point-free-involution-equiv-is-contr-fixed-point-free-involution A X e f t) = {!!}
```

## Examples

### The identity function is an involution

```agda
is-involution-id :
  {l : Level} {A : UU l} → is-involution (id {A = A})
is-involution-id = refl-htpy

id-involution :
  {l : Level} {A : UU l} → involution A
pr1 id-involution = id
pr2 id-involution = is-involution-id

involution-Pointed-Type :
  {l : Level} (A : UU l) → Pointed-Type l
pr1 (involution-Pointed-Type A) = involution A
pr2 (involution-Pointed-Type A) = id-involution
```
