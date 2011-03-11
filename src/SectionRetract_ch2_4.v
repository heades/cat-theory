Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.

(******************************************************************************)
(* Chapter 2.4: Sections and Retractions                                      *)
(******************************************************************************)

(* FIXME: do sections as well *)

Class RetractsInto `{C:Category} (A B:C) :=
{ retract_embed   : A~~{C}~~>B
; retract_project : B~~{C}~~>A
; retract_pf      : retract_embed >>> retract_project ~~ id _
}.
Notation "A ⊆ B" := (@RetractsInto _ _ _ A B) (at level 100).
Implicit Arguments retract_embed   [ Ob Hom C A B ].
Implicit Arguments retract_project [ Ob Hom C A B ].

(* Remark 2.14 *)
Instance FunctorsPreserveRetracts `{C:Category}`{D:Category}{Fobj}(F:Functor C D Fobj){a b:C}(r:a ⊆ b) : ((Fobj a) ⊆ (Fobj b)) :=
{ retract_embed   := F \ (retract_embed r)
; retract_project := F \ (retract_project r)
}.
  setoid_rewrite (fmor_preserves_comp F).
  setoid_rewrite retract_pf.
  apply fmor_preserves_id.
  Defined.

Instance iso_retract `{CX:Category}(a b:CX)(i:a ≅ b) : (a ⊆ b) :=
{ retract_embed   := iso_forward i
; retract_project := iso_backward i
}.
  apply (iso_comp1 i).
  Defined.

Instance retract_comp `{CX:Category}(a b c:CX)(r1:a ⊆ b)(r2:b ⊆ c) : (a ⊆ c) :=
{ retract_embed   := (retract_embed r1) >>> (retract_embed r2)
; retract_project := (retract_project r2) >>> (retract_project r1)
}.
  setoid_rewrite juggle3.
  setoid_rewrite retract_pf.
  setoid_rewrite right_identity.
  apply retract_pf.
  Defined.

Instance retract_prod `{C:Category}`{D:Category}{a b:C}{d e:D}(r1:a ⊆ b)(r2:d ⊆ e)
  : @RetractsInto _ _ (C ×× D) (pair_obj a d) (pair_obj b e) :=
{ retract_embed   := pair_mor (pair_obj a d) (pair_obj b e) (retract_embed   r1) (retract_embed   r2)
; retract_project := pair_mor (pair_obj b e) (pair_obj a d) (retract_project r1) (retract_project r2)
}.
  simpl; split; apply retract_pf.
  Defined.
