Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import ch1_3_Categories.
Require Import ch1_4_Functors.               
Require Import ch1_5_Isomorphisms.               

(*******************************************************************************)
(* Chapter 7.8: Equivalent Categories                                          *)
(*******************************************************************************)

(* Definition 7.24 *)
Class EquivalentCategories `(C:Category)`(D:Category){Fobj}{Gobj}(F:Functor C D Fobj)(G:Functor D C Gobj) :=
{ ec_forward  : F >>>> G ≃ functor_id C
; ec_backward : G >>>> F ≃ functor_id D
}.


(* FIXME *)
(* Definition 7.25: TFAE: F is an equivalence of categories, F is full faithful and essentially surjective *)
