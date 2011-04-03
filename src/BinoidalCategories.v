Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import Subcategories_ch7_1.

(******************************************************************************)
(* Binoidal Categories (not in Awodey)                                        *)
(******************************************************************************)

Class BinoidalCat
`( C                  :  Category                               )
( bin_obj'            :  C -> C -> C                            ) :=
{ bin_obj             := bin_obj' where "a ⊗ b" := (bin_obj a b)
; bin_first           :  forall a:C, Functor C C (fun x => x⊗a)
; bin_second          :  forall a:C, Functor C C (fun x => a⊗x)
; bin_c               := C
}.
Coercion bin_c : BinoidalCat >-> Category.
Notation "a ⊗ b"  := (@bin_obj _ _ _ _ _ a b)                              : category_scope.
Notation "C ⋊ f"  := (@fmor _ _ _ _ _ _ _ (@bin_second _ _ _ _ _ C) _ _ f) : category_scope.
Notation "g ⋉ C"  := (@fmor _ _ _ _ _ _ _ (@bin_first _ _ _ _ _ C) _ _ g)  : category_scope.
Notation "C ⋊ -"  := (@bin_second _ _ _ _ _ C)                             : category_scope.
Notation "- ⋉ C"  := (@bin_first _ _ _ _ _ C)                              : category_scope.

Class CentralMorphism `{BinoidalCat}`(f:a~>b) : Prop := 
{ centralmor_first  : forall `(g:c~>d), (f ⋉ _ >>> _ ⋊ g) ~~ (_ ⋊ g >>> f ⋉ _)
; centralmor_second : forall `(g:c~>d), (g ⋉ _ >>> _ ⋊ f) ~~ (_ ⋊ f >>> g ⋉ _)
}.

Class CommutativeCat `(BinoidalCat) :=
{ commutative_central  :  forall `(f:a~>b), CentralMorphism f
; commutative_morprod  := fun `(f:a~>b)`(g:a~>b) => f ⋉ _ >>> _ ⋊ g
}.
Notation "f × g"    := (commutative_morprod f g).

