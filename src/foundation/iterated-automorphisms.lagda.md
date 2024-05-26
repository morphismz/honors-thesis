# Iterated automorphisms

```agda
module foundation.iterated-automorphisms where
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
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces
```

</details>

## Idea

An automorphism of a type `X` is an equivalence `X ≃ X`. A 2-automorphism
is a homotopy `id {A = X} ~ id`. A 3-automorphism is a homotopy
`refl-htpy {f = id} ~ refl-htpy`. We can iterate this process.

## Definitions

Note that, in the below definition, the indices are off. From what may
be expected. `iterated-refl-htpy 0` is actually the identity function,
which is a 1-automorphism.

```agda
module _
  {l : Level} 
  where
  
  iterated-refl-htpy :
    (n : ℕ) {X : UU l} (x : X) → type-iterated-loop-space n (X , x)
  iterated-refl-htpy n x = iterated-refl-Ω n

  iterated-automorphism :
    (n : ℕ) (X : UU l) → UU l
  iterated-automorphism zero-ℕ X = X
  iterated-automorphism (succ-ℕ zero-ℕ) X = X ≃ X
  iterated-automorphism (succ-ℕ (succ-ℕ n)) X =
    iterated-refl-htpy n {X = X} ~ iterated-refl-htpy n

  iterated-automorphism-Pointed-Type :
    (n : ℕ) (X : Pointed-Type l) → Pointed-Type l
  iterated-automorphism-Pointed-Type zero-ℕ X = iterated-automorphism 0 (type-Pointed-Type X) , point-Pointed-Type X
  pr1 (iterated-automorphism-Pointed-Type (succ-ℕ zero-ℕ) X) =
    iterated-automorphism 1 (type-Pointed-Type X)
  pr1 (pr2 (iterated-automorphism-Pointed-Type (succ-ℕ zero-ℕ) X)) =
    iterated-refl-htpy 0
  pr2 (pr2 (iterated-automorphism-Pointed-Type (succ-ℕ zero-ℕ) X)) =
    is-equiv-id
  pr1 (iterated-automorphism-Pointed-Type (succ-ℕ (succ-ℕ n)) X) =
    iterated-automorphism (succ-ℕ (succ-ℕ n)) (type-Pointed-Type X)
  pr2 (iterated-automorphism-Pointed-Type (succ-ℕ (succ-ℕ n)) X) = iterated-refl-htpy (succ-ℕ n)
```
