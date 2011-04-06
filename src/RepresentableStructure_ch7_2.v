(*******************************************************************************)
(* Chapter 7.2: Representable Structure                                        *)
(*******************************************************************************)

Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import EpicMonic_ch2_1.
Require Import ProductCategories_ch1_6_1.
Require Import OppositeCategories_ch1_6_2.
Require Import Enrichment_ch2_8.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.
Require Import BinoidalCategories.
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch7_8.

Section RepresentableStructure.
  Context `(ec:ECategory(mn:=mn)(V:=V)).

  Definition hom_contravariant {a:ec}{d e:ec}(f:EI~~{V}~~>(d~~>e)) := #(pmon_cancell _)⁻¹ >>> (f ⋉ (_ ~~> a)) >>> ecomp.
  Definition hom_covariant     {a:ec}{d e:ec}(f:EI~~{V}~~>(d~~>e)) := #(pmon_cancelr _)⁻¹ >>> ((a ~~> d) ⋊ f) >>> ecomp.

  Lemma hom_covariant_distributes     {a b c:ec}{x}(f:a~~{ec}~~>b)(g:b~~{ec}~~>c)
     : hom_covariant (f >>> g) ~~ (hom_covariant (a:=x) f) >>> (hom_covariant g).
     set (f >>> g) as fg; simpl in fg; unfold fg; clear fg.
     unfold hom_covariant.
     repeat setoid_rewrite associativity.
     apply comp_respects; try reflexivity.
     set (@ecomp_is_functorial) as qq.
     repeat setoid_rewrite associativity in qq.
     apply qq.
     Qed.

  (*
  Lemma hom_swap {a b c d:ec}(f:a~~{ec}~~>b)(g:c~~{ec}~~>d)
     : hom_covariant f >>> hom_contravariant g ~~ hom_contravariant g >>> hom_covariant f.
     etransitivity.
     unfold hom_covariant.
     unfold hom_contravariant.
     Defined.     

  Definition YonedaBiFunctor_fmor (a b:ec⁽ºᑭ⁾ ×× ec)(f:a~~{ec⁽ºᑭ⁾ ×× ec}~~>b)
        : ((fst_obj _ _ a)~~>(snd_obj _ _ a))~~{V}~~>((fst_obj _ _ b)~~>(snd_obj _ _ b)).
    destruct a as [a1 a2].
    destruct b as [b1 b2].
    case f as [f1 f2]; intros.
    exact ( hom_contravariant (a:=a2) f1 >>> hom_covariant (a:=b1) f2 ).
    Defined.

  Definition YonedaBiFunctor : Functor (ec⁽ºᑭ⁾ ×× ec) V (fun a => (fst_obj _ _ a)~~>(snd_obj _ _ a)).
    refine {| fmor := fun a b f => YonedaBiFunctor_fmor a b f |}.
    abstract (intros; destruct a; destruct b; destruct f;
              destruct f';
              destruct H;
              repeat (apply comp_respects; try reflexivity); simpl;
              [ apply (@fmor_respects _ _ _ _ _ _ (fun x => (bin_obj x _))); auto
              | apply (fmor_respects ((o1 ~~> o0) ⋊-)); auto ]).
    abstract (
      destruct a; unfold YonedaBiFunctor_fmor;
      unfold hom_covariant;
      unfold hom_contravariant;
      etransitivity; simpl;
      [ apply comp_respects; setoid_rewrite associativity; simpl;
        [ etransitivity; [ apply comp_respects; [ reflexivity | apply eleft_identity ] | apply iso_comp2 ]
        | etransitivity; [ apply comp_respects; [ reflexivity | apply eright_identity ] | apply iso_comp2 ]
        ]
      | apply left_identity ]
      ).
    abstract (destruct a; destruct b; destruct c;
              destruct f;
              destruct g; unfold YonedaBiFunctor_fmor;
              setoid_rewrite juggle3;
              setoid_rewrite hom_swap;
              setoid_rewrite <- juggle3;
              setoid_rewrite <- hom_contravariant_distributes;
              setoid_rewrite <- hom_covariant_distributes;
              simpl;
              apply comp_respects;
              reflexivity).
    Defined.

  Definition HomFunctorºᑭ (X:ec) : Functor ec⁽ºᑭ⁾ V (fun a => a~~>X) := func_rlecnac X >>>> YonedaBiFunctor.
  *)

  Definition HomFunctor   (X:ec) : Functor ec     V (ehom X).
    refine {| fmor := @hom_covariant X |}.
    intros.
      unfold hom_covariant.
      apply comp_respects; try reflexivity.
      apply comp_respects; try reflexivity.
      apply fmor_respects; auto.
    intros.
      unfold hom_covariant.
      apply (epic _ (iso_epic ((pmon_cancelr) (X ~~> a)))).
      setoid_rewrite <- associativity.
      setoid_rewrite <- associativity.
      setoid_rewrite iso_comp1.
      setoid_rewrite left_identity.
      setoid_rewrite right_identity.
      apply (@eright_identity).
    intros.
      symmetry.
      apply hom_covariant_distributes.
      Defined.

  (*
  Lemma undo_homfunctor `(f:a~~{ec}~~>b) : f ~~ eid _ >>> (HomFunctor a \ f).
    simpl.
    setoid_rewrite <- associativity.
    unfold hom_contravariant.
    repeat setoid_rewrite <- associativity.
    setoid_rewrite juggle1.
    setoid_rewrite eleft_identity.
    repeat setoid_rewrite <- associativity.
    setoid_rewrite juggle1.
    setoid_rewrite iso_comp1.
    setoid_rewrite right_identity.
    unfold hom_covariant.
    repeat setoid_rewrite <- associativity.
    set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) (eid a)) as qq.
    simpl in qq.
    apply iso_shift_right' in qq.
    apply symmetry in qq.
    setoid_rewrite <- associativity in qq.
    apply iso_shift_left' in qq.
    apply symmetry in qq.
    setoid_rewrite qq.
    setoid_rewrite associativity.
    setoid_rewrite juggle3.
    setoid_rewrite (centralmor_first(CentralMorphism:=eid_central(ECategory:=ec) a)).
    repeat setoid_rewrite associativity.
    setoid_rewrite eleft_identity.
    set (ni_commutes (@pmon_cancell _ _ _ _ _ _ mn) f) as qqq.
    simpl in qqq.
    setoid_rewrite <- qqq.
    setoid_rewrite <- associativity.
    set (coincide pmon_triangle) as qqqq.
    setoid_rewrite qqqq.
    setoid_rewrite iso_comp1.
    setoid_rewrite left_identity.
    set (@eqv_equivalence) as qmt.
    apply qmt.
    Qed.
    *)

End RepresentableStructure.
Opaque HomFunctor.

