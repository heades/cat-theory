Generalizable All Variables.
Require Import Preamble.
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

(* not in Awodey *)
Class PreMonoidalCat `(bc:BinoidalCat(C:=C))(I:C) :=
{ pmon_I          := I
; pmon_bin        := bc
; pmon_cat        := C
; pmon_assoc      : forall a b, (bin_second a >>>> bin_first b) <~~~> (bin_first b >>>> bin_second a)
; pmon_cancelr    :                               (bin_first I) <~~~> functor_id C
; pmon_cancell    :                              (bin_second I) <~~~> functor_id C
; pmon_pentagon   : Pentagon (fun a b c f => f ⋉ c) (fun a b c f => c ⋊ f) (fun a b c => #((pmon_assoc a c) b))
; pmon_triangle   : Triangle (fun a b c f => f ⋉ c) (fun a b c f => c ⋊ f) (fun a b c => #((pmon_assoc a c) b))
                             (fun a => #(pmon_cancell a)) (fun a => #(pmon_cancelr a))
; pmon_assoc_rr   :  forall a b, (bin_first  (a⊗b)) <~~~> (bin_first  a >>>> bin_first  b)
; pmon_assoc_ll   :  forall a b, (bin_second (a⊗b)) <~~~> (bin_second b >>>> bin_second a)
; pmon_coherent_r :  forall a c d:C,  #(pmon_assoc_rr c d a) ~~ #(pmon_assoc a d c)⁻¹
; pmon_coherent_l :  forall a c d:C,  #(pmon_assoc_ll c a d) ~~ #(pmon_assoc c d a)
}.
(*
 * Premonoidal categories actually have three associators (the "f"
 * indicates the position in which the operation is natural:
 *
 *  assoc    : (A ⋊ f) ⋉ C <->  A ⋊ (f ⋉  C)
 *  assoc_rr : (f ⋉ B) ⋉ C <->  f ⋉ (B  ⊗ C)
 *  assoc_ll : (A ⋊ B) ⋊ f <-> (A ⊗  B) ⋊ f
 *
 * Fortunately, in a monoidal category these are all the same natural
 * isomorphism (and in any case -- monoidal or not -- the objects in
 * the left column are all the same and the objects in the right
 * column are all the same).  This formalization assumes that is the
 * case even for premonoidal categories with non-central maps, in
 * order to keep the complexity manageable.  I don't know much about
 * the consequences of having them and letting them be different; you
 * might need extra versions of the triangle/pentagon diagrams.
 *)

Implicit Arguments pmon_cancell [ Ob Hom C bin_obj' bc I ].
Implicit Arguments pmon_cancelr [ Ob Hom C bin_obj' bc I ].
Implicit Arguments pmon_assoc   [ Ob Hom C bin_obj' bc I ].
Coercion pmon_bin : PreMonoidalCat >-> BinoidalCat.

(* this turns out to be Exercise VII.1.1 from Mac Lane's CWM *)
Lemma MacLane_ex_VII_1_1 `{mn:PreMonoidalCat(I:=EI)} a b
  : #((pmon_cancelr mn) (a ⊗ b)) ~~ #((pmon_assoc mn a EI) b) >>> (a ⋊-) \ #((pmon_cancelr mn) b).
  set (pmon_pentagon EI EI a b) as penta. unfold pmon_pentagon in penta.
  set (pmon_triangle a b) as tria. unfold pmon_triangle in tria.
  apply (fmor_respects(bin_second EI)) in tria.
  set (@fmor_preserves_comp) as fpc.
  setoid_rewrite <- fpc in tria.
  set (ni_commutes (pmon_assoc mn a b)) as xx.
  (* FIXME *)
  Admitted.

Class PreMonoidalFunctor
`(PM1:PreMonoidalCat(C:=C1)(I:=I1))
`(PM2:PreMonoidalCat(C:=C2)(I:=I2))
 (fobj : C1 -> C2          ) :=
{ mf_F                :> Functor C1 C2 fobj
; mf_preserves_i      :  mf_F I1 ≅ I2
; mf_preserves_first  :  forall a,   bin_first a >>>> mf_F  <~~~>  mf_F >>>> bin_first  (mf_F a)
; mf_preserves_second :  forall a,  bin_second a >>>> mf_F  <~~~>  mf_F >>>> bin_second (mf_F a)
; mf_preserves_center :  forall `(f:a~>b), CentralMorphism f -> CentralMorphism (mf_F \ f)
}.
Coercion mf_F : PreMonoidalFunctor >-> Functor.

(*******************************************************************************)
(* Braided and Symmetric Categories                                            *)

Class BraidedCat `(mc:PreMonoidalCat) :=
{ br_niso        : forall a, bin_first a <~~~> bin_second a
; br_swap        := fun a b => ni_iso (br_niso b) a
; triangleb      : forall a:C,     #(pmon_cancelr mc a) ~~ #(br_swap a (pmon_I(PreMonoidalCat:=mc))) >>> #(pmon_cancell mc a)
; hexagon1       : forall {a b c}, #(pmon_assoc mc _ _ _) >>> #(br_swap a _) >>> #(pmon_assoc mc _ _ _)
                                   ~~ #(br_swap _ _) ⋉ c >>> #(pmon_assoc mc _ _ _) >>> b ⋊ #(br_swap _ _)
; hexagon2       : forall {a b c}, #(pmon_assoc mc _ _ _)⁻¹ >>> #(br_swap _ c) >>> #(pmon_assoc mc _ _ _)⁻¹
                                   ~~ a ⋊ #(br_swap _ _) >>> #(pmon_assoc mc _ _ _)⁻¹ >>> #(br_swap _ _) ⋉ b
}.

Class SymmetricCat `(bc:BraidedCat) :=
{ symcat_swap  :  forall a b:C, #((br_swap(BraidedCat:=bc)) a b) ~~ #(br_swap _ _)⁻¹
}.
