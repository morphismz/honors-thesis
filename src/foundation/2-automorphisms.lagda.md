# 2-automorphisms

```agda
module foundation.2-automorphisms where
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

A one dimensional automorphism, or just [automorphism](foundation.automorphisms.md),
of a type `X` is an [equivalence](foundation.equivalences.md) `X ≃ X`.
A two dimensional automorphism, or just 2-automorphism, of a type `X`
is a homotopy `id {A = X} ~ id` from the identitity function on `X` to itself.
The type of 2-automorphisms of `X` is equivalent to `Ω² (UU , X)`,
the [double loop space](synthetic-homotopy-theory.double-loop-spaces.md)
of the universe based at `X`.

## Definitions

```agda
module _
  {l : Level}
  where
  
  type-2-automorphism :
    UU l → UU l
  type-2-automorphism X = type-iterated-automorphism 2 X

  refl-htpy-2-automorphism :
    (X : UU l) → type-2-automorphism X
  refl-htpy-2-automorphism X = iterated-refl-htpy 1
```
