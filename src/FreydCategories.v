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
Require Import MonoidalCategories_ch7_8.

Class FreydCategory
{ Ob                          :  Type                                   }
{ freyd_bobj                  :  Ob -> Ob -> Ob                         }
{ HomC                        :  Ob -> Ob -> Type                       }
{ freyd_C                     :  Category Ob HomC                       }
{ freyd_C_terminal            :  Terminal    freyd_C                    }
{ freyd_C_binoidal            :  BinoidalCat freyd_C freyd_bobj         }
( freyd_C_monoidal            :  PreMonoidalCat freyd_C_binoidal 1         ) :=
{ freyd_K_hom                 :  Ob -> Ob -> Type
; freyd_K                     :> Category Ob freyd_K_hom
; freyd_C_cartesian           :  CartesianCat freyd_C_monoidal
; freyd_K_binoidal            :> BinoidalCat  freyd_K freyd_bobj
; freyd_K_monoidal            :> PreMonoidalCat  freyd_K_binoidal (one(Terminal:=freyd_C_terminal))
; freyd_K_braided             :  BraidedCat   freyd_K_monoidal
; freyd_K_symmetric           :  SymmetricCat freyd_K_braided
; freyd_F                     :> PreMonoidalFunctor freyd_C_monoidal freyd_K_monoidal (fun x => x)
; freyd_F_central             :  forall `(f:a~~{freyd_C}~~>b), CentralMorphism(C:=freyd_K) (freyd_F \ f)
; freyd_F_strict_first        : forall a b,   #(mf_preserves_first(PreMonoidalFunctor:=freyd_F) a b) ~~ id (bin_first a b)
; freyd_F_strict_second       : forall a b,   #(mf_preserves_second(PreMonoidalFunctor:=freyd_F) a b) ~~ id (bin_second a b)
; freyd_F_strict_a            : forall a b c, freyd_F \ #(pmon_assoc freyd_C_monoidal a b c) ~~ #(pmon_assoc freyd_K_monoidal _ _ _)
; freyd_F_strict_cl           :  forall a,     freyd_F \ #(pmon_cancell freyd_C_monoidal a) ~~ #(pmon_cancell freyd_K_monoidal _)
; freyd_F_strict_cr           :  forall a,     freyd_F \ #(pmon_cancelr freyd_C_monoidal a) ~~ #(pmon_cancelr freyd_K_monoidal _)
}.
Coercion freyd_K_monoidal : FreydCategory >-> PreMonoidalCat.
Coercion freyd_F          : FreydCategory >-> PreMonoidalFunctor.
Coercion freyd_K          : FreydCategory >-> Category.
