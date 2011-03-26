(*******************************************************************************)
(* Chapter 7.2: Representable Structure                                        *)
(*******************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import OppositeCategories_ch1_6_2.
Require Import Enrichment_ch2_8.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import MonoidalCategories_ch7_8.
Require Import Coherence_ch7_8.

(* FIXME: an object is a Generator if its covariant representable functor is faithful *)

Section RepresentableStructure.
  Context `(ec:ECategory(mn:=mn)(V:=V)).

  Definition hom_contravariant {a:ec}{d e:ec}(f:EI~~{V}~~>(d~~>e)) := #(pmon_cancell mn _)⁻¹ >>> (f ⋉ (_ ~~> a)) >>> ecomp.
  Definition hom_covariant     {a:ec}{d e:ec}(f:EI~~{V}~~>(d~~>e)) := #(pmon_cancelr mn _)⁻¹ >>> ((a ~~> d) ⋊ f) >>> ecomp.

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

  Lemma hom_contravariant_distributes {a b c:ec}{x}(f:a~~{ec}~~>b)(g:b~~{ec}~~>c)
     : hom_contravariant (f >>> g) ~~ (hom_contravariant g) >>> (hom_contravariant (a:=x) f).
     set (f >>> g) as fg; simpl in fg; unfold fg; clear fg.
     unfold hom_contravariant.
     repeat setoid_rewrite associativity.
     etransitivity; [ idtac | symmetry; apply associativity ].
     apply comp_respects; try reflexivity.
     set (@ecomp_is_functorial _ _ _ _ _ _ _ _ _ _ _ _ _ x f g) as qq.
     setoid_rewrite juggle2 in qq.
     admit.
     Qed.

  Lemma hom_swap {a b c d:ec}(f:a~~{ec}~~>b)(g:c~~{ec}~~>d)
     : hom_covariant f >>> hom_contravariant g ~~ hom_contravariant g >>> hom_covariant f.
     etransitivity.
     unfold hom_covariant.
     unfold hom_contravariant.
     Admitted.

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

  Definition RepresentableFunctorºᑭ (X:ec) : Functor ec⁽ºᑭ⁾ V (fun a => a~~>X) := func_rlecnac X >>>> YonedaBiFunctor.
  Definition RepresentableFunctor   (X:ec) : Functor ec     V (fun a => X~~>a) :=
    func_llecnac(C:=ec⁽ºᑭ⁾)(D:=ec) X >>>> YonedaBiFunctor.
  
  Lemma undo_homfunctor `(f:a~~{ec}~~>b) : f ~~ eid _ >>> (RepresentableFunctor a \ f).
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


End RepresentableStructure.
Opaque RepresentableFunctor.

Structure MonoidalEnrichment {e:Enrichment} :=
{ me_enr         :=e
; me_fobj        : prod_obj e e -> e
; me_f           : Functor (e ×× e) e me_fobj
; me_i           : e
; me_mon         : MonoidalCat e me_fobj me_f me_i
; me_mf          : MonoidalFunctor me_mon (enr_v_mon e) (RepresentableFunctor e me_i)
}.
Implicit Arguments MonoidalEnrichment [ ].
Coercion me_mon : MonoidalEnrichment >-> MonoidalCat.
Coercion me_enr : MonoidalEnrichment >-> Enrichment.

(* an enrichment for which hom(I,-) is monoidal, full, faithful, and conservative *)
Structure MonicMonoidalEnrichment {e}{me:MonoidalEnrichment e} :=
{ ffme_enr             := me
; ffme_mf_full         : FullFunctor         (RepresentableFunctor e (me_i me))
; ffme_mf_faithful     : FaithfulFunctor     (RepresentableFunctor e (me_i me))
; ffme_mf_conservative : ConservativeFunctor (RepresentableFunctor e (me_i me))
}.
Implicit Arguments MonicMonoidalEnrichment [ ].
Coercion ffme_enr : MonicMonoidalEnrichment >-> MonoidalEnrichment.
Transparent RepresentableFunctor.

Lemma CartesianEnrMonoidal (e:Enrichment) `(C:CartesianCat(Ob:= _)(Hom:= _)(C:=Underlying (enr_c e))) : MonoidalEnrichment e.
  admit.
  Defined.

Structure SurjectiveMonicMonoidalEnrichment (e:Enrichment) :=
{ smme_se       : SurjectiveEnrichment e
; smme_monoidal : MonoidalEnrichment e
; smme_me       : MonicMonoidalEnrichment _ smme_monoidal
}.
Coercion smme_se : SurjectiveMonicMonoidalEnrichment >-> SurjectiveEnrichment.
Coercion smme_me : SurjectiveMonicMonoidalEnrichment >-> MonicMonoidalEnrichment.

(* like SurjectiveMonicMonoidalEnrichment, but the Enrichment is a field, not a parameter *)
Structure SMME :=
{ smme_e   : Enrichment
; smme_mon : MonoidalEnrichment smme_e
; smme_me  : MonicMonoidalEnrichment smme_mon
}.
Coercion smme_e   : SMME >-> Enrichment.
Coercion smme_mon : SMME >-> MonoidalEnrichment smme_e.
Coercion smme_me  : SMME >-> MonicMonoidalEnrichment smme_mon.
