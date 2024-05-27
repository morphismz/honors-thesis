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
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-types

open import synthetic-homotopy-theory.dependent-2-loops
open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
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
  {l1 l2 : Level} {X : UU l1} (α : free-2-loop X)
  (B : X → UU l2)
  where

  free-dependent-2-loop : UU l2
  free-dependent-2-loop =
    Σ (B (base-free-2-loop α)) (λ b → dependent-2-loop (B , b) (2-loop-free-2-loop α))

module _
  {l1 l2 : Level} {X : UU l1} {B : X → UU l2}
  {α : free-2-loop X}
  where

  base-free-dependent-2-loop :
    free-dependent-2-loop α B → B (base-free-2-loop α)
  base-free-dependent-2-loop = pr1

  dependent-2-loop-free-dependent-2-loop :
    (β : free-dependent-2-loop α B) →
    dependent-2-loop (B , base-free-dependent-2-loop β) (2-loop-free-2-loop α)
  dependent-2-loop-free-dependent-2-loop = pr2
```

## Properties

### Characterization of the identity type of the type of free 2-loops

```agda
module _
  {l : Level} {X : UU l}
  where

  Eq-free-2-loop : (α α' : free-2-loop X) → UU l
  Eq-free-2-loop α α' =
    Σ (base-free-2-loop α ＝ base-free-2-loop α')
      ( λ p →
        map-tr-Ω² p (2-loop-free-2-loop α) ＝ 2-loop-free-2-loop α')

  refl-Eq-free-loop : (α : free-2-loop X) → Eq-free-2-loop α α
  pr1 (refl-Eq-free-loop α) = refl
  pr2 (refl-Eq-free-loop α) = inv (tr-Ω² refl (2-loop-free-2-loop α))
    
```

### A free dependent 2-loop determine a free 2-loop in the total space

```agda
module _
  {l1 l2 : Level} {X : UU l1} {B : X → UU l2}
  (α : free-2-loop X) (β : free-dependent-2-loop α B)
  where

  Eq²-Σ-free-dependent-2-loop :
    Eq²-Σ
      ( refl-Eq-Σ {B = B} (base-free-2-loop α , base-free-dependent-2-loop β))
      ( refl-Eq-Σ (base-free-2-loop α , base-free-dependent-2-loop β))
  pr1 Eq²-Σ-free-dependent-2-loop = 2-loop-free-2-loop α
  pr2 Eq²-Σ-free-dependent-2-loop =
    map-inv-equiv
      ( compute-dependent-2-loop
        ( B , base-free-dependent-2-loop β)
        ( 2-loop-free-2-loop α))
      ( dependent-2-loop-free-dependent-2-loop β)

  free-2-loop-total-space-free-dependent-2-loop :
    free-2-loop (Σ X B)
  pr1 (pr1 free-2-loop-total-space-free-dependent-2-loop) =
    base-free-2-loop α
  pr2 (pr1 free-2-loop-total-space-free-dependent-2-loop) =
    base-free-dependent-2-loop β
  pr2 free-2-loop-total-space-free-dependent-2-loop =
    map-inv-equiv (equiv-pair-eq²-Σ refl refl) Eq²-Σ-free-dependent-2-loop
```
