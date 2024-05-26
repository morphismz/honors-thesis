# Iterated automorphisms

```agda
module foundation.iterated-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces
```

</details>

## Idea

Given a type `X`, one my consider the [iterated loop spaces](synthetic-homotopy-theory.iterated-loop-spaces.md)
of the universe based at `X`, `(UU , X)`. By [univalence](foundation.univalence.md),
the first [loop space](synthetic-homotopy-theory.loop-spaces.md) `Ω (UU , X)` is equivalent to the type of [automorphisms](foundation.automorphisms.md)
of `X`, `X ≃ X`. By [function extensionality](foundation.function-extensionality.md),
the [double loop space](synthetic-homotopy-theory.double-loop-spaces.md)
`Ω² (UU , X)` is equivalent to the type of [2-automorphisms](foundation.2-automorphisms.md)
of `X`, `id ~ id`.

Extending this idea to `iterated-loop-space n (UU , X)` lends the notion
of the type of iterated automorphisms of `X`. We follow the "key
maneuver" of Licata and Brunerie {{#cite DLGB13}}, noting that

```text
(iterated-loop-space (n + 1) (UU , X)) ≃ ((x : X) → iterated-loop-space n (X , x))
```

## Definitions

Below we give two definitions. The first has better reduction behavior,
while the second is a more correct definition.

In the first definition, the indices are off by one from what may
be expected, and the definition for `n = 0` is incorrect..
The type `type-iterated-automorphism 0 X` is `X → X`, which
is almost `X ≃ X`, the type of 1-automorphisms. The type
`type-iterated-automorphism 1 X` is `id ~ id`, the type of 2-automorphisms.

```agda
module _
  {l : Level} 
  where

  type-iterated-automorphism :
    (n : ℕ) (X : UU l) → UU l
  type-iterated-automorphism n X =
    (x : X) → type-iterated-loop-space n (X , x)
  
  iterated-refl-htpy :
    (n : ℕ) {X : UU l} → type-iterated-automorphism n X
  iterated-refl-htpy n x = iterated-refl-Ω n

  iterated-automorphism :
    (n : ℕ) (X : Pointed-Type l) → Pointed-Type l
  iterated-automorphism zero-ℕ X = X
  pr1 (iterated-automorphism (succ-ℕ n) X) =
    type-iterated-automorphism (succ-ℕ n) (type-Pointed-Type X)
  pr2 (iterated-automorphism (succ-ℕ n) X) =
    iterated-refl-htpy (succ-ℕ n)
```

Here we give the second definition of the type of iterated automorphisms.
This definition is correct, at each level.

```agda
  type-iterated-automorphism' :
    (n : ℕ) (X : UU l) → UU l
  type-iterated-automorphism' zero-ℕ X = X
  type-iterated-automorphism' (succ-ℕ zero-ℕ) X = X ≃ X
  type-iterated-automorphism' (succ-ℕ (succ-ℕ n)) X =
    type-iterated-automorphism (succ-ℕ n) X

  iterated-automorphism' :
    (n : ℕ) (X : Pointed-Type l) → Pointed-Type l
  iterated-automorphism' zero-ℕ X = X
  pr1 (iterated-automorphism' (succ-ℕ zero-ℕ) X) =
    type-iterated-automorphism' 1 (type-Pointed-Type X)
  pr1 (pr2 (iterated-automorphism' (succ-ℕ zero-ℕ) X)) =
    iterated-refl-htpy 0
  pr2 (pr2 (iterated-automorphism' (succ-ℕ zero-ℕ) X)) =
    is-equiv-id
  pr1 (iterated-automorphism' (succ-ℕ (succ-ℕ n)) X) =
    type-iterated-automorphism' (succ-ℕ (succ-ℕ n)) (type-Pointed-Type X)
  pr2 (iterated-automorphism' (succ-ℕ (succ-ℕ n)) X) = iterated-refl-htpy (succ-ℕ n)
```

## References

{{#bibliography}} {{#reference DLGB13}}
