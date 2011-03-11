Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 2.2: Initial and Terminal Objects                                  *)
(******************************************************************************)

(* Definition 2.7 *)
Class Initial
`( C            : Category                         ) :=
{ zero          : C
; bottom        : forall a,  zero ~> a
; bottom_unique : forall `(f:zero~>a), f ~~ (bottom a)
}.
Notation "? A" := (bottom A)     : category_scope.
Notation "0"   := zero           : category_scope.

(* Definition 2.7 *)
Class Terminal
`( C          : Category                         ) :=
{ one         : C
; drop        : forall a,  a ~> one
; drop_unique : forall `(f:a~>one), f ~~ (drop a)
}.
Notation "! A" := (drop A)       : category_scope.
Notation "1"   := one            : category_scope.


(* Proposition 2.8 *)
(* FIXME: initial and terminal objects are unique up to iso *)

