# Free loops

```agda
module synthetic-homotopy-theory.free-2-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-families-of-types
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

  refl-Eq-free-2-loop : (α : free-2-loop X) → Eq-free-2-loop α α
  pr1 (refl-Eq-free-2-loop α) = refl
  pr2 (refl-Eq-free-2-loop α) = inv (tr-Ω² refl (2-loop-free-2-loop α))

  extensionality-free-2-loop :
    (α α' : free-2-loop X) → (α ＝ α') ≃ Eq-free-2-loop α α'
  extensionality-free-2-loop α =
    extensionality-Σ
      ( λ s p → map-tr-Ω² p (2-loop-free-2-loop α) ＝ s)
      ( refl)
      ( inv (tr-Ω² refl (2-loop-free-2-loop α)))
      ( λ x → id-equiv)
      ( λ y → equiv-concat (inv (tr-Ω² refl (2-loop-free-2-loop α))) y)

  Eq-eq-free-2-loop :
    (α α' : free-2-loop X) → α ＝ α' → Eq-free-2-loop α α'
  Eq-eq-free-2-loop α α' = map-equiv (extensionality-free-2-loop α α')

  eq-Eq-free-2-loop :
      (α α' : free-2-loop X) → Eq-free-2-loop α α' → α ＝ α'
  eq-Eq-free-2-loop α α' = map-inv-equiv (extensionality-free-2-loop α α')    
```

### A free 2-loop and a free dependent 2-loop are equivalent to a free 2-loop in the total space

```agda
module _
  {l1 l2 : Level} {X : UU l1} {B : X → UU l2}
  where

  Eq²-Σ-free-dependent-2-loop :
    ((α , β) : Σ (free-2-loop X) (λ α → free-dependent-2-loop α B)) →
    Eq²-Σ
      ( refl-Eq-Σ {B = B} (base-free-2-loop α , base-free-dependent-2-loop β))
      ( refl-Eq-Σ (base-free-2-loop α , base-free-dependent-2-loop β))
  pr1 (Eq²-Σ-free-dependent-2-loop (α , β)) = 2-loop-free-2-loop α
  pr2 (Eq²-Σ-free-dependent-2-loop (α , β)) =
    map-inv-equiv
      ( compute-dependent-2-loop
        ( B , base-free-dependent-2-loop β)
        ( 2-loop-free-2-loop α))
      ( dependent-2-loop-free-dependent-2-loop β)

  map-compute-free-2-loop-Σ :
    Σ (free-2-loop X) (λ α → free-dependent-2-loop α B) →
    free-2-loop (Σ X B)
  pr1 (pr1 (map-compute-free-2-loop-Σ (α , β))) =
    base-free-2-loop α
  pr2 (pr1 (map-compute-free-2-loop-Σ (α , β))) =
    base-free-dependent-2-loop β
  pr2 (map-compute-free-2-loop-Σ (α , β)) =
    map-inv-equiv
      ( equiv-pair-eq²-Σ refl refl)
      ( Eq²-Σ-free-dependent-2-loop (α , β))
    
module _
  {l1 l2 : Level} {X : UU l1} (B : X → UU l2)
  where

  compute-free-2-loop-Σ :
    ( Σ (free-2-loop X) (λ α → free-dependent-2-loop α B)) ≃
    ( free-2-loop (Σ X B))
  compute-free-2-loop-Σ =
    ( equiv-tot
      λ z →
        ( inv-equiv (equiv-pair-eq²-Σ refl refl)) ∘e
        ( equiv-tot
          λ α → inv-equiv (compute-dependent-2-loop (B , pr2 z) α))) ∘e
    ( interchange-Σ-Σ (λ x α b → dependent-2-loop (B , b) α))   

  inv-compute-free-2-loop-Σ :
    ( free-2-loop (Σ X B)) ≃
    ( Σ (free-2-loop X) (λ α → free-dependent-2-loop α B))
  inv-compute-free-2-loop-Σ =
    ( interchange-Σ-Σ ( λ x b α → dependent-2-loop (B , b) α)) ∘e
    ( equiv-tot
      λ (x , b) →
        ( ( equiv-tot
          λ α → compute-dependent-2-loop (B , b) α) ∘e
        ( equiv-pair-eq²-Σ refl refl)))

  map-compute-free-2-loop-Σ' :
    (α : free-2-loop  X) (β : free-dependent-2-loop α B) →
    free-2-loop (Σ X B)
  map-compute-free-2-loop-Σ' α β = map-compute-free-2-loop-Σ (α , β)
```

```agda
module _
  {l1 l2 : Level} {X : UU l1} (B : X → UU l2)
  where

  
```
