# Endomorphisms

```agda
module foundation.endomorphisms where

open import foundation-core.endomorphisms public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.wild-monoids
```

</details>

## Idea

An **endomorphism** on a type `A` is a map `A → A`.

## Properties

### Endomorphisms form a monoid

```agda
endo-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
pr1 (pr1 (endo-Wild-Monoid A)) = endo-Pointed-Type A
pr1 (pr2 (pr1 (endo-Wild-Monoid A))) g f = g ∘ f
pr1 (pr2 (pr2 (pr1 (endo-Wild-Monoid A)))) f = refl
pr1 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) = refl
pr1 (pr2 (endo-Wild-Monoid A)) h g f = refl
pr1 (pr2 (pr2 (endo-Wild-Monoid A))) g f = refl
pr1 (pr2 (pr2 (pr2 (endo-Wild-Monoid A)))) g f = refl
pr1 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) g f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) = star

endo-Semigroup : {l : Level} → Set l → Semigroup l
pr1 (endo-Semigroup A) = endo-Set A
pr1 (pr2 (endo-Semigroup A)) g f = g ∘ f
pr2 (pr2 (endo-Semigroup A)) h g f = refl

endo-Monoid : {l : Level} → Set l → Monoid l
pr1 (endo-Monoid A) = endo-Semigroup A
pr1 (pr2 (endo-Monoid A)) = id
pr1 (pr2 (pr2 (endo-Monoid A))) f = refl
pr2 (pr2 (pr2 (endo-Monoid A))) f = refl
```

### Fixed point free endomorphisms

```agda
module _
  {l : Level} (X : UU l)
  where

  is-fixed-point-free-endomorphism :
    (X → X) → UU l
  is-fixed-point-free-endomorphism f =
    ((x : X) → ¬ (f x ＝ x))

  fixed-point-free-endomorphism :
    UU l
  fixed-point-free-endomorphism = Σ (X → X) is-fixed-point-free-endomorphism
```

### The subtype of fixed point free endomorphisms

```agda
  is-subtype-is-fixed-point-free-endomorphism :
    is-subtype is-fixed-point-free-endomorphism
  is-subtype-is-fixed-point-free-endomorphism f =
    is-prop-Π λ x → is-prop-neg

  subtype-fixed-point-free-endomorphism :
    subtype l (X → X)
  pr1 (subtype-fixed-point-free-endomorphism f) =
    is-fixed-point-free-endomorphism f
  pr2 (subtype-fixed-point-free-endomorphism f) =
    is-subtype-is-fixed-point-free-endomorphism f
```

## See also

- For endomorphisms in a category see
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).
