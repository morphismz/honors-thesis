# Free loops

```agda
module synthetic-homotopy-theory.free-2-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.dependent-2-loops
open import synthetic-homotopy-theory.double-loop-spaces
```

</details>

## Idea

A **free 2-loop** in a type `X` consists of a point `x` in ` X` and
a [2-loop](synthetic-homotopy-theory.double-loop-spaces.md) `α : Ω² (X , x)`.
The type of free loops in `X` is equivalent to maps from the 2-sphere
into `X`.


## Definitions

### Free 2-loops

```agda
module _
  {l : Level} (X : UU l)
  where

  free-2-loop : UU l
  free-2-loop = Σ X (λ x → type-Ω² x)

module _
  {l : Level} {X : UU l}
  where

  base-free-2-loop : free-2-loop X → X
  base-free-2-loop = pr1

  2-loop-free-2-loop : (α : free-2-loop X) → type-Ω² (base-free-2-loop α)
  2-loop-free-2-loop = pr2
```

### Dependent free 2-loops

```agda
module _
  {l1 l2 : Level} {X : Pointed-Type l1} (B : type-Pointed-Type X → UU l2)
  (α : type-Ω² (point-Pointed-Type X))
  where

  free-dependent-2-loop : UU l2
  free-dependent-2-loop =
    Σ (B (point-Pointed-Type X)) (λ b → dependent-2-loop (B , b) α )

module _
  {l1 l2 : Level} {X : Pointed-Type l1} {B : type-Pointed-Type X → UU l2}
  {α : type-Ω² (point-Pointed-Type X)}
  where

  base-free-dependent-2-loop :
    free-dependent-2-loop B α → B (point-Pointed-Type X)
  base-free-dependent-2-loop = pr1

  dependent-2-loop-free-dependent-2-loop :
    (β : free-dependent-2-loop B α) →
    dependent-2-loop (B , base-free-dependent-2-loop β) α
  dependent-2-loop-free-dependent-2-loop = pr2
```
