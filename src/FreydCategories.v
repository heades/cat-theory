(*******************************************************************************)
(* Freyd Categories                                                            *)
(*******************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import InitialTerminal_ch2_2.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import Coherence_ch7_8.
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import PreMonoidalCenter.
Require Import MonoidalCategories_ch7_8.

(* A Freyd Category is... *)
Class FreydCategory

  (* a cartesian category C *)
  `(C:CartesianCat(Ob:=Ob)(C:=C1))

  (* a premonoidal category K with the same objects (its unit object is 1 because the functor is both IIO and strict) *)
  `(K:PreMonoidalCat(Ob:=Ob)(bin_obj':=bobj)(I:=@one _ _ _ C))

  (* an identity-on-objects functor J:C->Z(K) *)
:= { fc_J       : Functor C (Center_is_Monoidal K) (fun x => exist (fun _ => True) x I)

  (* which is not only monoidal *)
   ; fc_mf_J    : MonoidalFunctor C (Center_is_Monoidal K) fc_J

   (* but in fact strict (meaning the functor's coherence maps are identities) *)
   (*; fc_strict  : forall a b, #(mf_first a b) ~~ id _ 
         FIXME - I will need to separate Subcategory from FullSubCategory in order to fix this *)

   ; fc_C       := C
   ; fc_K       := K
   }.

Coercion fc_mf_J   : FreydCategory >-> MonoidalFunctor.
Coercion fc_K      : FreydCategory >-> PreMonoidalCat.

