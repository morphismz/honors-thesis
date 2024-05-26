# Dependent 3-loops

```agda
module synthetic-homotopy-theory.dependent-3-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-higher-identifications
open import foundation.universe-levels

open import structured-types.pointed-families-of-types
open import structured-types.pointed-types

open import synthetic-homotopy-theory.triple-loop-spaces
```

</details>

## Idea

Consider a [pointed type](structured-types.pointed-types.md) `(X , x)`
along with a [pointed family of types over `(X , x)'](structured-types.pointed-families-of-types.md),
`(B : X → UU , b : B x)`. Fix a [3-loop](synthetic-homotopy-theory.triple-loop-spaces.md)
in `X`, `α : Ω³ (X , x)`. Then a dependent 3-loop in `B` based at `b` over `α`
consits of an identification `tr³ B α b ＝ refl`.

## Definition

```agda
module _
  {l1 l2 : Level} {X : Pointed-Type l1} (B : Pointed-Fam l2 X)
  where

  dependent-3-loop :
    (α : type-Ω³ (point-Pointed-Type X)) → UU l2
  dependent-3-loop α =
    tr³ (fam-Pointed-Fam X B) α (point-Pointed-Fam X B) ＝ refl
```
