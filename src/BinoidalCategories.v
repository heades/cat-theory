Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
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

Section BinoidalCat_from_Bifunctor.
  Context `{C:Category}{Fobj}(F:Functor (C ×× C) C Fobj).
  Definition BinoidalCat_from_Bifunctor_first (a:C) : Functor C C (fun b => Fobj (pair_obj b a)).
  apply Build_Functor with (fmor:=(fun a0 b (f:a0~~{C}~~>b) =>
    @fmor _ _ _ _ _ _ _ F (pair_obj a0 a) (pair_obj b a) (pair_mor (pair_obj a0 a) (pair_obj b a) f (id a)))); intros; simpl;
    [ abstract (set (fmor_respects(F)) as q; apply q; split; simpl; auto)
    | abstract (set (fmor_preserves_id(F)) as q; apply q)
    | abstract (etransitivity; 
      [ set (@fmor_preserves_comp _ _ _ _ _ _ _ F) as q; apply q
      | set (fmor_respects(F)) as q; apply q ];
      split; simpl; auto) ].
  Defined.
  Definition BinoidalCat_from_Bifunctor_second (a:C) : Functor C C (fun b => Fobj (pair_obj a b)).
  apply Build_Functor with (fmor:=(fun a0 b (f:a0~~{C}~~>b) =>
    @fmor _ _ _ _ _ _ _ F (pair_obj a a0) (pair_obj a b) (pair_mor (pair_obj a a0) (pair_obj a b) (id a) f))); intros;
    [ abstract (set (fmor_respects(F)) as q; apply q; split; simpl; auto)
    | abstract (set (fmor_preserves_id(F)) as q; apply q)
    | abstract (etransitivity; 
      [ set (@fmor_preserves_comp _ _ _ _ _ _ _ F) as q; apply q
      | set (fmor_respects(F)) as q; apply q ];
      split; simpl; auto) ].
  Defined.

  Definition BinoidalCat_from_Bifunctor : BinoidalCat C (fun a b => Fobj (pair_obj a b)).
   refine {| bin_first  := BinoidalCat_from_Bifunctor_first
           ; bin_second := BinoidalCat_from_Bifunctor_second
          |}.
   Defined.

  Lemma Bifunctors_Create_Commutative_Binoidal_Categories : CommutativeCat BinoidalCat_from_Bifunctor.
  abstract (intros; apply Build_CommutativeCat; intros; apply Build_CentralMorphism; intros; simpl; (
    etransitivity; [ apply (fmor_preserves_comp(F)) | idtac ]; symmetry;
    etransitivity; [ apply (fmor_preserves_comp(F)) | idtac ];
    apply (fmor_respects(F));
    split;
      [ etransitivity; [ apply left_identity | symmetry; apply right_identity ]
      | etransitivity; [ apply right_identity | symmetry; apply left_identity ] ])).
  Defined.

End BinoidalCat_from_Bifunctor.
