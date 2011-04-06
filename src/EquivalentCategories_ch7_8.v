(*******************************************************************************)
(* Chapter 7.8: Equivalent Categories                                          *)
(*******************************************************************************)

Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import NaturalIsomorphisms_ch7_5.

(* Definition 7.24 *)
Class EquivalentCategories `(C:Category)`(D:Category){Fobj}{Gobj}(F:Functor C D Fobj)(G:Functor D C Gobj) :=
{ ec_forward  : F >>>> G ≃ functor_id C
; ec_backward : G >>>> F ≃ functor_id D
}.


(* FIXME *)
(* Definition 7.25: TFAE: F is an equivalence of categories, F is full faithful and essentially surjective *)
