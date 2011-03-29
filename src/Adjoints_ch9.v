Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.

(*******************************************************************************)
(* Chapter 9: Adjoints                                                         *)
(*******************************************************************************)

Class Adjunction `{C:Category}`{D:Category}{Fobj}{Gobj}(L:Functor D C Fobj)(R:Functor C D Gobj) :=
{ adj_counit : functor_id D ~~~> L >>>> R
; adj_unit   : R >>>> L          ~~~> functor_id C
; adj_pf1    : forall (X:C)(Y:D), id (L Y) ~~ (L \ (adj_counit Y)) >>> (adj_unit (L Y))
; adj_pf2    : forall (X:C)(Y:D), id (R X) ~~ (adj_counit (R X)) >>> (R \ (adj_unit X))
(* FIXME: use the definition based on whiskering *)
}.
Notation "L -| R" := (Adjunction L R).
Notation "'ε'"    := (adj_counit _).
Notation "'η'"    := (adj_unit _).

(* Definition 9.6 "Official" *)
(*
Lemma homset_adjunction `(C:ECategory(V:=V))`(D:ECategory(V:=V))(L:Func C D)(R:Func D C)
 :  (L -| R)
 -> HomFunctorºᑭ _ _ >>>> YonedaBiFunctor D ≃
    HomFunctorºᑭ _ _ >>>> YonedaBiFunctor C.
  *)
  (* adjuncts are unique up to natural iso *)
  (* adjuncts compose *)
  (* adjuncts preserve limits *)
  (* every adjunction determines a monad, vice versa *)
  (* E-M category *)
  (* Kleisli category *)
  (* if C is enriched, then we get an iso of hom-sets *)




(* Example 9.7: exopnentiation is right adjoint to product *)

(* Example 9.8: terminal object selection is right adjoint to the terminal-functor in Cat *)

(* Proposition 9.9: Adjoints are unique up to iso *)

(* Example 9.9: Product is left adjoint to diagonal, and coproduct is right adjoint; generalizes to limits/colimits *)


(* Proposition 9.14: RAPL *)



