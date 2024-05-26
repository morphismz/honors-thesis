# Dependent 2-loops

```agda
module synthetic-homotopy-theory.dependent-2-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-higher-identifications
open import foundation.universe-levels

open import structured-types.pointed-families-of-types
open import structured-types.pointed-types

open import synthetic-homotopy-theory.double-loop-spaces
```

</details>

## Idea

Consider a [pointed type](structured-types.pointed-types.md) `(X , x)`
along with a [pointed family of types over `(X , x)'](structured-types.pointed-families-of-types.md),
`(B : X → UU , b : B x)`. Fixed a [2-loop](synthetic-homotopy-theory.double-loop-spaces.md)
in `X`, `α : Ω² (X , x)`. Then a dependent 2-loop in `B` based at `b` over `α`
consits of an identification `tr² B α b ＝ refl`.

## Definition

```agda
module _
  {l1 l2 : Level} {X : Pointed-Type l1} (B : Pointed-Fam l2 X)
  where

  dependent-2-loop :
    (α : type-Ω² (point-Pointed-Type X)) → UU l2
  dependent-2-loop α =
    tr² (fam-Pointed-Fam X B) α (point-Pointed-Fam X B) ＝ refl
```
