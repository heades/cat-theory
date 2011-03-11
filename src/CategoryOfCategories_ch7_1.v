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
Require Import MonoidalCategories_ch7_8.
Require Import Enrichment_ch2_8.

(*******************************************************************************)
(* Category of Categories enriched in some fixed category V                    *)

Section CategoryOfCategories.

  Context {VOb}{VHom}(V:Category VOb VHom){VI}{MFobj}{MF}(VM:MonoidalCat V VI MFobj MF).

  Class ECat :=
  { ecat_obj :  Type
  ; ecat_hom :  ecat_obj -> ecat_obj -> VOb
  ; ecat_cat :> ECategory VM ecat_obj ecat_hom
  }.
  Implicit Arguments ecat_obj [ ].
  Implicit Arguments ecat_cat [ ].
  Implicit Arguments ecat_hom [ ].
  Instance ToECat {co}{ch}(c:ECategory VM co ch) : ECat := { ecat_cat := c }.

  Class EFunc (C1 C2:ECat) :=
  { efunc_fobj    : ecat_obj C1 -> ecat_obj C2
  ; efunc_functor : EFunctor (ecat_cat C1) (ecat_cat C2) efunc_fobj
  }.
  Implicit Arguments efunc_fobj    [ C1 C2 ].
  Implicit Arguments efunc_functor [ C1 C2 ].
  Instance ToEFunc {C1}{C2}{eo}(F:EFunctor (ecat_cat C1) (ecat_cat C2) eo)
     : EFunc C1 C2 := { efunc_functor := F }.

  (* FIXME: should be enriched in whatever V is enriched in *)
  Instance CategoryOfCategories : Category ECat EFunc :=
  { id    := fun c                                     => ToEFunc (efunctor_id (ecat_cat c))
(*  ; eqv   := fun c1 c2 f1 f2                           => f1 ≃ f2 *)
  ; comp  := fun c1 c2 c3 (g:EFunc c1 c2)(f:EFunc c2 c3) => ToEFunc (efunctor_comp _ _ _ (efunc_functor g) (efunc_functor f))
  }.
  admit.
  admit.
  admit.
  Defined.

  (* FIXME: show that subcategories are monos in __Cat__ *)

End CategoryOfCategories.
