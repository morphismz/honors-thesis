# Universal Property of suspensions of pointed types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import structured-types.constant-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [suspension](synthetic-homotopy-theory.suspensions-of-types.md) of a
[pointed type](structured-types.pointed-types.md) enjoys an additional universal
property, on top of
[the universal property associtated with being a suspension](synthetic-homotopy-theory.universal-property-suspensions.md).
This universal property is packaged in an adjunction: the suspension
construction on pointed types is left adjoint to the loop space construction.

#### The unit and counit of the adjunction

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  pointed-equiv-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) ≃∗
    ( Ω (suspension-Pointed-Type X))
  pointed-equiv-loop-pointed-identity-suspension =
    pointed-equiv-loop-pointed-identity
      ( suspension-Pointed-Type X)
      ( meridian-suspension (point-Pointed-Type X))

  pointed-map-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) →∗
    Ω (suspension-Pointed-Type X)
  pointed-map-loop-pointed-identity-suspension =
    pointed-map-pointed-equiv
      ( pointed-equiv-loop-pointed-identity-suspension)

  pointed-map-concat-meridian-suspension :
    X →∗
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X)))
  pr1 pointed-map-concat-meridian-suspension = meridian-suspension
  pr2 pointed-map-concat-meridian-suspension = refl

  pointed-map-unit-suspension-loop-adjunction :
    X →∗ Ω (suspension-Pointed-Type X)
  pointed-map-unit-suspension-loop-adjunction =
    pointed-map-loop-pointed-identity-suspension ∘∗
    pointed-map-concat-meridian-suspension

  map-unit-suspension-loop-adjunction :
    type-Pointed-Type X → type-Ω (suspension-Pointed-Type X)
  map-unit-suspension-loop-adjunction =
    map-pointed-map pointed-map-unit-suspension-loop-adjunction

  map-counit-suspension-loop-adjunction :
    suspension (type-Ω X) → type-Pointed-Type X
  map-counit-suspension-loop-adjunction =
    map-inv-is-equiv
      ( up-suspension (type-Pointed-Type X))
      ( point-Pointed-Type X , point-Pointed-Type X , id)

  pointed-map-counit-suspension-loop-adjunction :
    pair (suspension (type-Ω X)) (north-suspension) →∗ X
  pr1 pointed-map-counit-suspension-loop-adjunction =
    map-counit-suspension-loop-adjunction
  pr2 pointed-map-counit-suspension-loop-adjunction =
    compute-north-cogap-suspension
      ( point-Pointed-Type X , point-Pointed-Type X , id)
```

#### The transposing maps of the adjunction

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) → (X →∗ Ω Y)
  transpose-suspension-loop-adjunction f∗ =
    pointed-map-Ω f∗ ∘∗ pointed-map-unit-suspension-loop-adjunction X

  htpy-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction :
    ( map-pointed-map
      ( transpose-suspension-loop-adjunction
        ( constant-pointed-map (suspension-Pointed-Type X) Y))) ~
    ( map-pointed-map
      ( constant-pointed-map X (Ω Y)))
  htpy-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction =
    (htpy-preserves-constant-pointed-map-pointed-map-Ω (suspension-Pointed-Type X) Y) ·r (map-unit-suspension-loop-adjunction X) ∙h
    htpy-pointed-htpy (comp-left-constant-pointed-map (pointed-map-unit-suspension-loop-adjunction X))

--- DEFINE GENERAL INFRASTRUCTURE FOR CONCATINATION AND WHISKERING OF POINTED HOMOTOPIES TO AVOID THIS NEXT STEP

  coherence-point-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction :
    coherence-point-unpointed-htpy-pointed-Π
      ( transpose-suspension-loop-adjunction
        ( constant-pointed-map (suspension-Pointed-Type X) Y))
      ( constant-pointed-map X (Ω Y))
      ( htpy-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction)
  coherence-point-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction =
    {!!}

  pointed-htpy-preserves-point-transpose-suspension-loop-adjunction :
    pointed-htpy
      ( transpose-suspension-loop-adjunction
        ( constant-pointed-map (suspension-Pointed-Type X) Y))
      ( constant-pointed-map X (Ω Y))
  pr1 pointed-htpy-preserves-point-transpose-suspension-loop-adjunction =
    htpy-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction
  pr2 pointed-htpy-preserves-point-transpose-suspension-loop-adjunction =
    coherence-point-pointed-htpy-preserves-point-transpose-suspension-loop-adjunction

  preserves-point-transpose-suspension-loop-adjunction :
    ( transpose-suspension-loop-adjunction
      ( constant-pointed-map (suspension-Pointed-Type X) Y)) ＝
    ( constant-pointed-map X (Ω Y))
  preserves-point-transpose-suspension-loop-adjunction =
    eq-pointed-htpy
      ( transpose-suspension-loop-adjunction
        ( constant-pointed-map (suspension-Pointed-Type X) Y))
      ( constant-pointed-map X (Ω Y))
      ( pointed-htpy-preserves-point-transpose-suspension-loop-adjunction)
    
  pointed-map-transpose-suspension-loop-adjunction :
    pointed-map-Pointed-Type (suspension-Pointed-Type X) Y →∗
    pointed-map-Pointed-Type X (Ω Y)
  pr1 pointed-map-transpose-suspension-loop-adjunction = transpose-suspension-loop-adjunction
  pr2 pointed-map-transpose-suspension-loop-adjunction = preserves-point-transpose-suspension-loop-adjunction
  
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  inv-transpose-suspension-loop-adjunction :
    (X →∗ Ω Y) → (suspension-Pointed-Type X →∗ Y)
  pr1 (inv-transpose-suspension-loop-adjunction f∗) =
    cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
  pr2 (inv-transpose-suspension-loop-adjunction f∗) =
    compute-north-cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
```

We now show these maps are inverses of each other.

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction :
    (f∗ : X →∗ Ω Y) →
    map-pointed-map
      ( ( ( transpose-suspension-loop-adjunction X Y) ∘
        ( inv-transpose-suspension-loop-adjunction X Y))
          ( f∗)) ~
    map-pointed-map f∗
  htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗ x =
    ( compute-map-Ω
      ( inv-transpose-suspension-loop-adjunction X Y f∗)
      ( map-unit-suspension-loop-adjunction X x)) ∙
    ( assoc
      ( inv
        (preserves-point-pointed-map
          ( inv-transpose-suspension-loop-adjunction X Y f∗)))
      ( ap
        ( map-pointed-map
          ( inv-transpose-suspension-loop-adjunction X Y f∗))
          ( map-unit-suspension-loop-adjunction X x))
      ( preserves-point-pointed-map
        ( inv-transpose-suspension-loop-adjunction X Y f∗))) ∙ 
    ( left-transpose-eq-concat'
      ( ( ap
          ( map-pointed-map
            ( inv-transpose-suspension-loop-adjunction X Y f∗))
          ( map-unit-suspension-loop-adjunction X x)) ∙
        ( preserves-point-pointed-map
          ( inv-transpose-suspension-loop-adjunction X Y f∗)))
      ( preserves-point-pointed-map
        ( inv-transpose-suspension-loop-adjunction X Y f∗))
      ( map-pointed-map f∗ x)
      ( inv-concat-left-identification-coherence-square-identifications
        ( preserves-point-pointed-map
          ( inv-transpose-suspension-loop-adjunction X Y f∗))
        ( ap
          ( map-pointed-map
            ( inv-transpose-suspension-loop-adjunction X Y f∗))
          ( ( meridian-suspension x) ∙ inv (meridian-suspension (point-Pointed-Type X))))
        ( map-pointed-map f∗ x)
        ( compute-north-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( Y)
            ( map-pointed-map f∗)))
        ( ( ap-concat
            ( map-pointed-map
              ( inv-transpose-suspension-loop-adjunction X Y f∗))
            ( meridian-suspension x)
            ( inv (meridian-suspension (point-Pointed-Type X)))) ∙
          ( left-whisker-concat
            ( ap
              (map-pointed-map (inv-transpose-suspension-loop-adjunction X Y f∗))
              ( meridian-suspension x))
            ( ap-inv
              ( map-pointed-map
                ( inv-transpose-suspension-loop-adjunction X Y f∗))
              ( meridian-suspension (point-Pointed-Type X)))))
        ( concat-right-identification-coherence-square-identifications
          ( preserves-point-pointed-map
            ( inv-transpose-suspension-loop-adjunction X Y f∗))
          ( ( ap
              ( map-pointed-map
                ( inv-transpose-suspension-loop-adjunction X Y f∗))
              ( meridian-suspension x)) ∙
            ( inv
              ( ap
                ( map-pointed-map
                  ( inv-transpose-suspension-loop-adjunction X Y f∗))
                ( meridian-suspension (point-Pointed-Type X)))))
          ( ( map-pointed-map f∗ x) ∙
            ( inv (map-pointed-map f∗ (point-Pointed-Type X))))
          ( preserves-point-pointed-map
            ( inv-transpose-suspension-loop-adjunction X Y f∗))
          ( ( left-whisker-concat
              ( map-pointed-map f∗ x)
              (ap inv ( preserves-point-pointed-map f∗))) ∙
            ( right-unit))
          ( vertical-pasting-coherence-square-identifications
            ( preserves-point-pointed-map
              ( inv-transpose-suspension-loop-adjunction X Y f∗))
            ( ap
              ( map-pointed-map
                ( inv-transpose-suspension-loop-adjunction X Y f∗))
              ( meridian-suspension x))
            ( map-pointed-map f∗ x)
            ( compute-south-cogap-suspension
              ( suspension-structure-map-into-Ω
                ( type-Pointed-Type X)
                ( Y)
                ( map-pointed-map f∗)))
            ( inv
              ( ap
                ( map-pointed-map
                  ( inv-transpose-suspension-loop-adjunction X Y f∗))
                ( meridian-suspension (point-Pointed-Type X))))
            ( inv (map-pointed-map f∗ (point-Pointed-Type X)))
            ( preserves-point-pointed-map
              ( inv-transpose-suspension-loop-adjunction X Y f∗))
            ( compute-meridian-cogap-suspension
              ( suspension-structure-map-into-Ω
                ( type-Pointed-Type X)
                ( Y)
                ( map-pointed-map f∗))
              ( x))
            ( vertical-inv-coherence-square-identifications
              ( preserves-point-pointed-map
                ( inv-transpose-suspension-loop-adjunction X Y f∗))
              ( ap
                ( map-pointed-map
                  ( inv-transpose-suspension-loop-adjunction X Y f∗))
                ( meridian-suspension (point-Pointed-Type X)))
              ( map-pointed-map f∗ (point-Pointed-Type X))
              ( compute-south-cogap-suspension
                ( suspension-structure-map-into-Ω
                  ( type-Pointed-Type X)
                  ( Y)
                  ( map-pointed-map f∗)))
              ( compute-meridian-cogap-suspension
                ( suspension-structure-map-into-Ω
                  ( type-Pointed-Type X)
                  ( Y)
                  ( map-pointed-map f∗))
                ( point-Pointed-Type X)))))))

  compute-point-htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction :
    (f∗ : X →∗ Ω Y) →
    htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗ (point-Pointed-Type X) ＝ {!!}
  compute-point-htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction = {!!}

  coherence-point-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction :
    (f∗ : X →∗ Ω Y) →
    coherence-point-unpointed-htpy-pointed-Π
      ( ( ( transpose-suspension-loop-adjunction X Y) ∘
        ( inv-transpose-suspension-loop-adjunction X Y))
          ( f∗))
      ( f∗)
      ( htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗)
  coherence-point-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗ =
    {!!}
        
  pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction :
    (f∗ : X →∗ Ω Y) →
    pointed-htpy
      ( ( ( transpose-suspension-loop-adjunction X Y) ∘
        ( inv-transpose-suspension-loop-adjunction X Y))
          ( f∗))
      ( f∗)
  pr1 (pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗) =
    htpy-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗
  pr2 (pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗) =
    coherence-point-pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗

  is-section-inv-transpose-suspension-loop-adjunction :
    ( ( transpose-suspension-loop-adjunction X Y) ∘
      ( inv-transpose-suspension-loop-adjunction X Y)) ~
    ( id)
  is-section-inv-transpose-suspension-loop-adjunction f∗ =
    eq-pointed-htpy
      ( ( ( transpose-suspension-loop-adjunction X Y) ∘
        ( inv-transpose-suspension-loop-adjunction X Y))
          ( f∗))
      ( f∗)
      ( pointed-htpy-is-section-inv-transpose-suspension-loop-adjunction f∗)

  htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
    htpy-function-out-of-suspension
      ( type-Pointed-Type X)
      ( map-pointed-map
        ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
          ( transpose-suspension-loop-adjunction X Y))
            ( f∗)))
       ( map-pointed-map f∗)
  pr1 (htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction (f , refl)) =
    compute-north-cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( type-Pointed-Type Y , f north-suspension)
        ( map-pointed-map
          ( transpose-suspension-loop-adjunction
            ( X)
            ( type-Pointed-Type Y , f north-suspension)
            ( f , refl))))
  pr1 (pr2 (htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction (f , refl))) =
    ( compute-south-cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( type-Pointed-Type Y , f north-suspension)
        ( map-pointed-map
          ( transpose-suspension-loop-adjunction
            ( X)
            ( type-Pointed-Type Y , f north-suspension)
            ( f , refl))))) ∙
    ( ap f (meridian-suspension (point-Pointed-Type X)))
  pr2 (pr2 (htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction (f , refl))) x =
    concat-top-identification-coherence-square-identifications
      ( ( compute-north-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( type-Pointed-Type Y , f north-suspension)
            ( map-pointed-map
              ( transpose-suspension-loop-adjunction
                ( X)
                ( type-Pointed-Type Y , f north-suspension)
                ( f , refl))))) ∙
        ( refl))
      ( ap
        ( map-pointed-map
          ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
            ( transpose-suspension-loop-adjunction X Y))
              ( f , refl)))
        ( meridian-suspension x))
      ( ap f (meridian-suspension x))
      ( ( compute-south-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( type-Pointed-Type Y , f north-suspension)
            ( map-pointed-map
              ( transpose-suspension-loop-adjunction
                ( X)
                ( type-Pointed-Type Y , f north-suspension)
                ( f , refl))))) ∙
        ( ap f (meridian-suspension (point-Pointed-Type X))))
      ( right-unit)
      ( horizontal-pasting-coherence-square-identifications
        ( compute-north-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( type-Pointed-Type Y , f north-suspension)
            ( map-pointed-map
              ( transpose-suspension-loop-adjunction
                ( X)
                ( type-Pointed-Type Y , f north-suspension)
                ( f , refl)))))
        ( refl)
        ( ap
          ( map-pointed-map
            ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
              ( transpose-suspension-loop-adjunction X Y))
                ( f , refl)))
          ( meridian-suspension x))
        ( map-pointed-map
          ( transpose-suspension-loop-adjunction X Y ( f , refl))
          ( x))
        ( ap f (meridian-suspension x))
        ( compute-south-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( type-Pointed-Type Y , f north-suspension)
            ( map-pointed-map
              ( transpose-suspension-loop-adjunction
                ( X)
                ( type-Pointed-Type Y , f north-suspension)
                ( f , refl)))))
        ( ap f (meridian-suspension (point-Pointed-Type X)))
        ( compute-meridian-cogap-suspension
          ( suspension-structure-map-into-Ω
            ( type-Pointed-Type X)
            ( type-Pointed-Type Y , f north-suspension)
            ( map-pointed-map
              ( transpose-suspension-loop-adjunction
                ( X)
                ( type-Pointed-Type Y , f north-suspension)
                ( f , refl))))
          ( x))
        ( ( right-whisker-concat
            ( ap-concat
              ( f)
              ( meridian-suspension x)
              (inv (meridian-suspension (point-Pointed-Type X))))
            ( ap f (meridian-suspension (point-Pointed-Type X)))) ∙
          ( double-whisker-concat
            ( ap f (meridian-suspension x))
            ( ap-inv f (meridian-suspension (pr2 X)))
            ( ap f (meridian-suspension (pr2 X)))) ∙
          ( ( assoc
              ( ap f (meridian-suspension x))
              ( inv (ap f (meridian-suspension (pr2 X))))
              ( ap f (meridian-suspension (pr2 X))))) ∙
          ( left-whisker-concat
            ( ap f (meridian-suspension x))
            ( left-inv (ap f (meridian-suspension (pr2 X))))  ) ∙
          ( right-unit)))

  htpy-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
    ( map-pointed-map
      ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
        ( transpose-suspension-loop-adjunction X Y))
          ( f∗))) ~
     ( map-pointed-map f∗)
  htpy-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗ =
    htpy-htpy-function-out-of-suspension
      (type-Pointed-Type X)
      ( map-pointed-map
        ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
          ( transpose-suspension-loop-adjunction X Y))
            f∗))
      ( map-pointed-map f∗)
      ( htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗)
      

  coherence-point-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
     coherence-point-unpointed-htpy-pointed-Π
       ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
         ( transpose-suspension-loop-adjunction X Y))
           ( f∗))
       ( f∗)
       ( htpy-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗)
  coherence-point-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction (f , refl) =
    inv
      ( ( right-unit) ∙
        ( ( compute-north-htpy-htpy-function-out-of-suspension
          ( type-Pointed-Type X)
          ( map-pointed-map
            ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
              ( transpose-suspension-loop-adjunction X Y))
                ( f , refl)))
          ( f )
          ( htpy-function-out-of-suspension-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction (f , refl)))))

  pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction :
    (f∗ : suspension-Pointed-Type X →∗ Y) → 
    pointed-htpy
      ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
        ( transpose-suspension-loop-adjunction X Y))
          ( f∗))
      ( f∗)
  pr1 (pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗) =
    htpy-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗ 
  pr2 (pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗) =
    coherence-point-pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗

  is-retraction-inv-transpose-suspension-loop-adjunction :
    ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
      ( transpose-suspension-loop-adjunction X Y)) ~
      ( id)
  is-retraction-inv-transpose-suspension-loop-adjunction f∗ =
    eq-pointed-htpy
      ( ( ( inv-transpose-suspension-loop-adjunction X Y) ∘
        ( transpose-suspension-loop-adjunction X Y))
          ( f∗))
      ( f∗)
      ( pointed-htpy-is-retraction-inv-transpose-suspension-loop-adjunction f∗)
```

#### The transposing equivalence between pointed maps out of the suspension of `X` and pointed maps into the loop space of `Y`

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  is-equiv-transpose-suspension-loop-adjunction :
    is-equiv (transpose-suspension-loop-adjunction X Y)
  is-equiv-transpose-suspension-loop-adjunction =
    is-equiv-is-invertible
      ( inv-transpose-suspension-loop-adjunction X Y)
      ( is-section-inv-transpose-suspension-loop-adjunction X Y)
      ( is-retraction-inv-transpose-suspension-loop-adjunction X Y)

  equiv-transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  pr1 equiv-transpose-suspension-loop-adjunction =
    transpose-suspension-loop-adjunction X Y
  pr2 equiv-transpose-suspension-loop-adjunction =
    is-equiv-transpose-suspension-loop-adjunction
```

#### The equivalence in the suspension-loop space adjunction is pointed

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  is-pointed-equiv-transpose-suspension-loop-adjunction :
    is-pointed-equiv (pointed-map-transpose-suspension-loop-adjunction X Y)
  is-pointed-equiv-transpose-suspension-loop-adjunction = {!!}

  pointed-equiv-transpose-suspension-loop-adjunction :
    ( pointed-map-Pointed-Type (suspension-Pointed-Type X) Y) ≃∗
    ( pointed-map-Pointed-Type X (Ω Y))
  pr1 pointed-equiv-transpose-suspension-loop-adjunction =
    equiv-transpose-suspension-loop-adjunction X Y
  pr2 pointed-equiv-transpose-suspension-loop-adjunction =
    preserves-point-transpose-suspension-loop-adjunction X Y
```

This remains to be shown.
[#702](https://github.com/UniMath/agda-unimath/issues/702)
