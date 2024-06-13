# Constant pointed maps

```agda
module structured-types.constant-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `A` and `B` the
{{#concept "constant pointed map" Agda=constant-pointed-map}} from `A` to `B` is
the [pointed map](structured-types.pointed-maps.md)
`constant-pointed-map : A →∗ B` mapping every element in `A` to the base point
of `B`.

## Definitions

### Constant pointed maps

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-constant-pointed-map : type-Pointed-Type A → type-Pointed-Type B
  map-constant-pointed-map =
    const (type-Pointed-Type A) (point-Pointed-Type B)

  preserves-point-constant-pointed-map :
    map-constant-pointed-map (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-constant-pointed-map = refl

  constant-pointed-map : A →∗ B
  pr1 constant-pointed-map = map-constant-pointed-map
  pr2 constant-pointed-map = preserves-point-constant-pointed-map
```

### The pointed type of pointed maps

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  pr1 pointed-map-Pointed-Type = A →∗ B
  pr2 pointed-map-Pointed-Type = constant-pointed-map A B
```

## Properties

### The action on paths of a constant pointed map

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  {x y : type-Pointed-Type A}
  where

  ap-constant-pointed-map :
    (p : x ＝ y) → ap (map-constant-pointed-map A B) p ＝ refl
  ap-constant-pointed-map p = ap-const (point-Pointed-Type B) p
```

### Composing a contanstant pointed map with any other pointed map lends a constant pointed map

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  comp-left-constant-pointed-map :
    (f : A →∗ B) →
    pointed-htpy
      ( constant-pointed-map B C ∘∗ f)
      ( constant-pointed-map A C)
  pr1 (comp-left-constant-pointed-map f) = refl-htpy
  pr2 (comp-left-constant-pointed-map f) =
    right-unit ∙ ap-constant-pointed-map B C (preserves-point-pointed-map f)

  comp-right-constant-pointed-map :
    (f : B →∗ C) →
    pointed-htpy
      ( f ∘∗ constant-pointed-map A B)
      ( constant-pointed-map A C)
  pr1 (comp-right-constant-pointed-map f) a =
    preserves-point-pointed-map f
  pr2 (comp-right-constant-pointed-map f) = inv right-unit
```

## See also

- [Constant maps](foundation.constant-maps.md)
