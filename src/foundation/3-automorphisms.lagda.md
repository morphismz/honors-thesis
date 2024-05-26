# 2-automorphisms

```agda
module foundation.3-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-automorphisms
open import foundation.universe-levels

open import structured-types.pointed-types

```

</details>

## Idea

A one dimensional automorphism, or [automorphism](foundation.automorphisms.md),
of a type `X` is an [equivalence](foundation.equivalences.md) `X ≃ X`.
A two dimensional automorphism, or [2-automorphism](foundation.2-automorphism.md), of a type `X`
is a homotopy `H : id {A = X} ~ id` from the identitity function on `X` to itself.
A three dimensional automorphism, or 3-automorphism, is a homotopy
`H : refl-htpy {f = id} ~ refl-htpy` from the trival homotopy on the identity
function to itself.

The type of 3-automorphisms is naturally a pointed-type with base point
`refl-htpy {f = refl-htpy}`, or `iterated-refl-htpy 2`.
By [univalence](foundation.univalence.md), this pointed type of
3-automorphisms of `X` is equivalent to `Ω³ (UU , X)`,
the [triple loop space](synthetic-homotopy-theory.triple-loop-spaces.md)
of the universe based at `X`.

## Definitions

```agda
module _
  {l : Level}
  where

  type-3-automorphism :
    UU l → UU l
  type-3-automorphism X = type-iterated-automorphism 3 X

  refl-htpy-3-automorphism :
    {X : UU l} → type-3-automorphism X
  refl-htpy-3-automorphism = iterated-refl-htpy 2

  3-automorphism :
    UU l → Pointed-Type l
  pr1 (3-automorphism X) = type-3-automorphism X
  pr2 (3-automorphism X) = refl-htpy-3-automorphism
```
