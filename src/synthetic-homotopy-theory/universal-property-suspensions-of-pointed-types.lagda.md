# Universal Property of suspensions of pointed types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

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

#### The transposing equivalence between pointed maps out of the suspension of `X` and pointed maps into the loop space of `Y`

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-transpose-suspension-loop-adjunction =
    ( left-unit-law-Σ-is-contr
      ( is-torsorial-Id (point-Pointed-Type Y))
      ( point-Pointed-Type Y , refl)) ∘e
    ( inv-associative-Σ
      ( type-Pointed-Type Y)
      ( λ z → point-Pointed-Type Y ＝ z)
      ( λ t →
        Σ ( type-Pointed-Type X → point-Pointed-Type Y ＝ pr1 t)
          ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
    ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
    ( associative-Σ
      ( type-Pointed-Type Y)
      ( λ y1 → type-Pointed-Type X → point-Pointed-Type Y ＝ y1)
      ( λ z →
        Σ ( point-Pointed-Type Y ＝ pr1 z)
          ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
    ( inv-right-unit-law-Σ-is-contr
      ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X)))) ∘e
    ( left-unit-law-Σ-is-contr
      ( is-torsorial-Id' (point-Pointed-Type Y))
      ( point-Pointed-Type Y , refl)) ∘e
    ( equiv-right-swap-Σ) ∘e
    ( equiv-Σ-equiv-base
      ( λ c → pr1 c ＝ point-Pointed-Type Y)
      ( equiv-up-suspension))

-- WONT LOAD UNTILL YOU FINISH SPECIAL CASE IN type-arithmetic-dependent-pair-types

  equiv-test :
    (suspension-Pointed-Type X →∗ Y) ≃ (Σ (Σ (type-Pointed-Type Y) (λ y → point-Pointed-Type Y ＝ y)) λ (y , p) → Σ (type-Pointed-Type X → point-Pointed-Type Y ＝ y) (λ m → m (point-Pointed-Type X) ＝ p))
  equiv-test =
    ( inv-associative-Σ
        ( type-Pointed-Type Y)
        ( λ z → point-Pointed-Type Y ＝ z)
        ( λ t →
          Σ ( type-Pointed-Type X → point-Pointed-Type Y ＝ pr1 t)
            ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
      ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
      ( associative-Σ
        ( type-Pointed-Type Y)
        ( λ y1 → type-Pointed-Type X → point-Pointed-Type Y ＝ y1)
        ( λ z →
          Σ ( point-Pointed-Type Y ＝ pr1 z)
            ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
      ( inv-right-unit-law-Σ-is-contr
        ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X)))) ∘e
      ( left-unit-law-Σ-is-contr
        ( is-torsorial-Id' (point-Pointed-Type Y))
        ( point-Pointed-Type Y , refl)) ∘e
      ( equiv-right-swap-Σ) ∘e
      ( equiv-Σ-equiv-base
        ( λ c → pr1 c ＝ point-Pointed-Type Y)
        ( equiv-up-suspension))

module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : UU l2)
  (f : suspension (type-Pointed-Type X) → Y)
  where

  shit-fuck₁ :
    map-equiv
      ( ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ-equiv-base (λ c → pr1 c ＝ f north-suspension) (equiv-up-suspension)))
      ( f , refl) ＝
    ((f north-suspension , refl) , (f south-suspension , ap f ∘ meridian-suspension))
  shit-fuck₁ = refl    

  shit-fuck₂ :
    map-equiv
      ( ( left-unit-law-Σ-is-contr
          ( is-torsorial-Id' (f north-suspension))
          ( f north-suspension , refl)) ∘e 
        ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ-equiv-base (λ c → pr1 c ＝ f north-suspension) (equiv-up-suspension)))
      ( f , refl) ＝
    (f south-suspension , ap f ∘ meridian-suspension)
  shit-fuck₂ = equational-reasoning
    ( map-equiv
      ( ( left-unit-law-Σ-is-contr
          ( is-torsorial-Id' (f north-suspension))
          ( f north-suspension , refl)) ∘e 
        ( equiv-right-swap-Σ) ∘e
        ( equiv-Σ-equiv-base (λ c → pr1 c ＝ f north-suspension) (equiv-up-suspension)))
      ( f , refl))
    ＝ ( map-left-unit-law-Σ-is-contr
        {B = λ (x , p) → Σ Y (λ y → type-Pointed-Type X → x ＝ y)}
        ( is-torsorial-Id' (f north-suspension))
        ( f north-suspension , refl)
        ( (f north-suspension , refl) , (f south-suspension , ap f ∘ meridian-suspension)))
      by
      refl
    ＝ (f south-suspension , ap f ∘ meridian-suspension)
      by
      ( htpy-eq
        ( special-case'
          { B = λ x → Σ Y (λ y → type-Pointed-Type X → x ＝ y)}
          ( f north-suspension) refl)
        ( f south-suspension , ap f ∘ meridian-suspension))


  shit-fuck₃ :
    map-equiv
      ( inv-right-unit-law-Σ-is-contr
        { A = Σ Y (λ y → type-Pointed-Type X → f north-suspension ＝ y)}
        ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X))))
      ( f south-suspension , ap f ∘ meridian-suspension) ＝
    ( ( f south-suspension , ap f ∘ meridian-suspension) , (ap f (meridian-suspension (point-Pointed-Type X)) , refl))
  shit-fuck₃ =
    eq-pair-Σ
      refl
      ( equational-reasoning
        center (is-torsorial-Id (ap f (meridian-suspension (point-Pointed-Type X))))
        ＝ (ap f (meridian-suspension (point-Pointed-Type X)) , refl)
          by
          contraction
            (is-torsorial-Id (ap f (meridian-suspension (point-Pointed-Type X))))
            (ap f (meridian-suspension (point-Pointed-Type X)) , refl))
  
  htpy-test₂ :
    ( map-equiv (equiv-test X (Y , f (point-Pointed-Type (suspension-Pointed-Type X)))) (f , refl)) ＝
    ( ( f south-suspension , ap f (meridian-suspension (point-Pointed-Type X))) , (ap f ∘ meridian-suspension , refl))
  htpy-test₂ = equational-reasoning
    ( map-equiv
      ( equiv-test X (Y , f (point-Pointed-Type (suspension-Pointed-Type X))))
      ( f , refl))
    ＝ ( map-equiv
        ( ( inv-associative-Σ
            ( Y)
            ( λ z → f north-suspension ＝ z)
            ( λ t →
              Σ ( type-Pointed-Type X → f north-suspension ＝ pr1 t)
                ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
          ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
          ( associative-Σ
            ( Y)
            ( λ y1 → type-Pointed-Type X → f north-suspension ＝ y1)
            ( λ z →
              Σ ( f north-suspension ＝ pr1 z)
                ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
          ( inv-right-unit-law-Σ-is-contr
            ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X)))))
        ( f south-suspension , ap f ∘ meridian-suspension))
      by
      ( ap
        ( map-equiv
          ( ( inv-associative-Σ
              ( Y)
              ( λ z → f north-suspension ＝ z)
              ( λ t →
                Σ ( type-Pointed-Type X → f north-suspension ＝ pr1 t)
                  ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
            ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
            ( associative-Σ
              ( Y)
              ( λ y1 → type-Pointed-Type X → f north-suspension ＝ y1)
              ( λ z →
                Σ ( f north-suspension ＝ pr1 z)
                  ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
            ( inv-right-unit-law-Σ-is-contr
              ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X))))))
        ( shit-fuck₂))
    ＝ ( map-equiv
         ( ( inv-associative-Σ
             ( Y)
             ( λ z → f north-suspension ＝ z)
             ( λ t →
               Σ ( type-Pointed-Type X → f north-suspension ＝ pr1 t)
                 ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
           ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
           ( associative-Σ
             ( Y)
             ( λ y1 → type-Pointed-Type X → f north-suspension ＝ y1)
             ( λ z →
               Σ ( f north-suspension ＝ pr1 z)
                 ( λ x → pr2 z (point-Pointed-Type X) ＝ x))))
         ( ( f south-suspension , ap f ∘ meridian-suspension)
           , (ap f (meridian-suspension (point-Pointed-Type X)) , refl)) )
      by
      ap
        ( map-equiv
          ( ( inv-associative-Σ
              ( Y)
              ( λ z → f north-suspension ＝ z)
              ( λ t →
                Σ ( type-Pointed-Type X → f north-suspension ＝ pr1 t)
                  ( λ f → f (point-Pointed-Type X) ＝ pr2 t))) ∘e
            ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
            ( associative-Σ
              ( Y)
              ( λ y1 → type-Pointed-Type X → f north-suspension ＝ y1)
              ( λ z →
                Σ ( f north-suspension ＝ pr1 z)
                  ( λ x → pr2 z (point-Pointed-Type X) ＝ x)))))
        ( shit-fuck₃)    
    ＝ ( ( ( f south-suspension)
          , ( ap f (meridian-suspension (point-Pointed-Type X))))
       , ( ap f ∘ meridian-suspension , refl))
      by
      refl

  htpy-test₃ :
    ( map-equiv (equiv-transpose-suspension-loop-adjunction X (Y , f (point-Pointed-Type (suspension-Pointed-Type X)))) (f , refl)) ＝
    ( {!!})
  htpy-test₃ = {!!}

module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where


  htpy-test :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
    ( map-pointed-map (transpose-suspension-loop-adjunction X Y f∗)) ~
    ( map-pointed-map (map-equiv (equiv-transpose-suspension-loop-adjunction X Y) f∗))
  htpy-test (f , refl) x = equational-reasoning
    ap
      ( f)
      ( ( meridian-suspension x) ∙
        ( inv (meridian-suspension (point-Pointed-Type X))))
    ＝ ( ( ap
           ( f)
           ( meridian-suspension x)) ∙
         ( ap
           ( f)
           ( inv (meridian-suspension (point-Pointed-Type X)))))
      by
      ap-concat
        ( f)
        ( meridian-suspension x)
        ( inv (meridian-suspension (point-Pointed-Type X)))
    ＝ ( ( ap
           ( f)
           ( meridian-suspension x)) ∙
         ( inv
           ( ap
             ( f)
             ( meridian-suspension (point-Pointed-Type X)))))
      by
      left-whisker-concat
        ( ap
          ( f)
          ( meridian-suspension x))
        ( ap-inv
          ( f)
          ( meridian-suspension (point-Pointed-Type X)))
    ＝ tr
        ( Id (point-Pointed-Type Y))
        ( inv (ap f (meridian-suspension (point-Pointed-Type X))))
        ( ap f (meridian-suspension x))
      by
      inv
        ( tr-Id-right
          ( inv (ap f (meridian-suspension (point-Pointed-Type X))))
          ( ap f (meridian-suspension x)))
    ＝ tr
        ( λ y → type-Pointed-Type X → Id (point-Pointed-Type Y) y)
        ( inv (ap f (meridian-suspension (point-Pointed-Type X))))
        ( ap f ∘ meridian-suspension)
        ( x)
      by
      inv
        ( htpy-eq
          ( tr-function-type-fixed-domain
            ( type-Pointed-Type X)
            ( Id (point-Pointed-Type Y))
            ( inv (ap f (meridian-suspension (point-Pointed-Type X))))
            (ap f ∘ meridian-suspension))
          ( x))
    ＝ {!!}
      by
      {!!}
    ＝ {!!}
      by
      {!!}
    ＝ map-pointed-map (map-equiv (equiv-transpose-suspension-loop-adjunction X Y) (f , refl)) x
      by
      {!!}

{-

tr-function-type-fixed-domain

tr-function-type (const (type-Pointed-Type Y) (type-Pointed-Type X)) (λ y → (point-Pointed-Type Y) ＝ y) (ap f (inv (meridian-suspension (point-Pointed-Type X)))) (ap f ∘ meridian-suspension) -}

{-  coh-point-htpy-test :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
    coherence-point-unpointed-htpy-pointed-Π
      ( transpose-suspension-loop-adjunction X Y f∗)
      ( map-equiv (equiv-transpose-suspension-loop-adjunction X Y) f∗)
      ( htpy-test f∗)
  coh-point-htpy-test = {!!}

  pointed-htpy-test :
    (f∗ : suspension-Pointed-Type X →∗ Y) →
    ( transpose-suspension-loop-adjunction X Y f∗) ~∗
    ( map-equiv (equiv-transpose-suspension-loop-adjunction X Y) f∗)
  pr1 (pointed-htpy-test f∗) = htpy-test f∗
  pr2 (pointed-htpy-test f∗) = coh-point-htpy-test f∗

  test :
    ( transpose-suspension-loop-adjunction X Y) ~  
    ( map-equiv (equiv-transpose-suspension-loop-adjunction X Y))
  test f∗ =
    eq-pointed-htpy
      ( transpose-suspension-loop-adjunction X Y f∗)
      ( map-equiv (equiv-transpose-suspension-loop-adjunction X Y) f∗)
      ( pointed-htpy-test f∗)-}
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.
[#702](https://github.com/UniMath/agda-unimath/issues/702)
