Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import InitialTerminal_ch2_2.
Require Import Subcategories_ch7_1.
Require Import ProductCategories_ch1_6_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import Coherence_ch7_8.
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.

(******************************************************************************)
(* Chapter 7.8: Monoidal Categories                                           *)
(******************************************************************************)

(* TO DO: show that the endofunctors on any given category form a monoidal category *)

(*
 * Unlike Awodey, I define a monoidal category to be a premonoidal
 * category in which all morphisms are central.  This is partly to
 * have a clean inheritance hierarchy, but also because Coq bogs down
 * on product categories for some inexplicable reason.
 *)
Class MonoidalCat `(pm:PreMonoidalCat) :=
{ mon_pm          := pm
; mon_commutative :> CommutativeCat pm
}.
Coercion mon_pm          : MonoidalCat >-> PreMonoidalCat.
Coercion mon_commutative : MonoidalCat >-> CommutativeCat.

(* a monoidal functor is just a premonoidal functor between premonoidal categories which happen to be monoidal *)
Definition MonoidalFunctor `(m1:MonoidalCat) `(m2:MonoidalCat) {fobj}(F:Functor m1 m2 fobj) := PreMonoidalFunctor m1 m2 F.

Definition MonoidalFunctorsCompose
  `{PM1   :MonoidalCat(C:=C1)}
  `{PM2   :MonoidalCat(C:=C2)}
   {fobj12:C1 -> C2                    }
   {PMFF12:Functor C1 C2 fobj12        }
   (PMF12 :MonoidalFunctor PM1 PM2 PMFF12)
  `{PM3   :MonoidalCat(C:=C3)}
   {fobj23:C2 -> C3                    }
   {PMFF23:Functor C2 C3 fobj23        }
   (PMF23 :MonoidalFunctor PM2 PM3 PMFF23)
   := PreMonoidalFunctorsCompose PMF12 PMF23.

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

  (* if this binoidal structure has all of the natural isomorphisms of a premonoidal category, then it's monoidal *)
  Context {pmI}(pm:PreMonoidalCat BinoidalCat_from_Bifunctor pmI).

  Instance PreMonoidalCat_from_bifunctor_is_Monoidal : MonoidalCat pm :=
  { mon_commutative := Bifunctors_Create_Commutative_Binoidal_Categories
  }.

End BinoidalCat_from_Bifunctor.


(* we can go the other way: given a monoidal category, its left/right functors can be combined into a bifunctor *)
Section Bifunctor_from_MonoidalCat.
  Context `(M:MonoidalCat).


  Definition Bifunctor_from_MonoidalCat_fobj : M ×× M -> M.
    intro x.
    destruct x.
    exact (bin_obj' o o0).
    Defined.

  Definition Bifunctor_from_MonoidalCat_fmor {a}{b}(f:a~~{M××M}~~>b)
    : (Bifunctor_from_MonoidalCat_fobj a)~~{M}~~>(Bifunctor_from_MonoidalCat_fobj b).
    destruct a; destruct b; destruct f.
    simpl in *.
    apply (h ⋉ _ >>> _ ⋊ h0).
    Defined.

  Instance Bifunctor_from_MonoidalCat : Functor (M ×× M) M Bifunctor_from_MonoidalCat_fobj :=
    { fmor := fun x y f => Bifunctor_from_MonoidalCat_fmor f }.
    intros; simpl.
    destruct a; destruct b; destruct f; destruct f'; simpl in *.
    destruct H.
    apply comp_respects.
      apply (fmor_respects (-⋉o0)); auto.
      apply (fmor_respects (o1⋊-)); auto.
    intros; destruct a; simpl in *.
      setoid_rewrite (fmor_preserves_id (-⋉o0)).
      setoid_rewrite left_identity.
      apply fmor_preserves_id.
    intros; destruct a; destruct b; destruct c; destruct f; destruct g; simpl in *.
      setoid_rewrite <- fmor_preserves_comp.
      setoid_rewrite juggle3 at 1.
      assert (CentralMorphism h1).
        apply mon_commutative.
      setoid_rewrite <- (centralmor_first(CentralMorphism:=H)).
      setoid_rewrite <- juggle3.
      reflexivity.
      Defined.

End Bifunctor_from_MonoidalCat.


Class DiagonalCat `(mc:MonoidalCat) :=
{ copy          :  forall (a:mc),   a~~{mc}~~>(bin_obj(BinoidalCat:=mc) a a)
; copy_natural1 :  forall {a}{b}(f:a~~{mc}~~>b)(c:mc), copy _ >>> f ⋉ a >>> b ⋊ f ~~ f >>> copy _
; copy_natural2 :  forall {a}{b}(f:a~~{mc}~~>b)(c:mc), copy _ >>> a ⋊ f >>> f ⋉ b ~~ f >>> copy _
(* for non-cartesian braided diagonal categories we also need: copy >> swap == copy *)
}.

Class CartesianCat `(mc:MonoidalCat) :=
{ car_terminal  :> TerminalObject mc pmon_I
; car_diagonal  :  DiagonalCat mc
; car_law1      :  forall {a}, id a ~~ (copy(DiagonalCat:=car_diagonal) a) >>> (drop a  ⋉ a) >>> (#(pmon_cancell _))
; car_law2      :  forall {a}, id a ~~ (copy(DiagonalCat:=car_diagonal) a) >>> (a ⋊ drop  a) >>> (#(pmon_cancelr _))
; car_mn        := mc
}.
Coercion car_diagonal : CartesianCat >-> DiagonalCat.
Coercion car_terminal : CartesianCat >-> TerminalObject.
Coercion car_mn       : CartesianCat >-> MonoidalCat.
