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
Require Import PreMonoidalCategories.
Require Import MonoidalCategories_ch_7_8.

(******************************************************************************)
(* Facts about the center of a Binoidal or PreMonoidal Category               *)
(******************************************************************************)

Lemma central_morphisms_compose `{bc:BinoidalCat}{a b c}(f:a~>b)(g:b~>c)
  : CentralMorphism f -> CentralMorphism g -> CentralMorphism (f >>> g).
  intros.
  apply Build_CentralMorphism; intros.
  abstract (setoid_rewrite <- (fmor_preserves_comp(bin_first c0));
              setoid_rewrite associativity;
              setoid_rewrite centralmor_first;
              setoid_rewrite <- associativity;
              setoid_rewrite centralmor_first;
              setoid_rewrite associativity;
              setoid_rewrite <- (fmor_preserves_comp(bin_first d));
              reflexivity).
  abstract (setoid_rewrite <- (fmor_preserves_comp(bin_second d));
              setoid_rewrite <- associativity;
              setoid_rewrite centralmor_second;
              setoid_rewrite associativity;
              setoid_rewrite centralmor_second;
              setoid_rewrite <- associativity;
              setoid_rewrite <- (fmor_preserves_comp(bin_second c0));
              reflexivity).
  Qed.

(* the central morphisms of a category constitute a subcategory *)
Definition Center `(bc:BinoidalCat) : SubCategory bc (fun _ => True) (fun _ _ _ _ f => CentralMorphism f).
  apply Build_SubCategory; intros.
  apply Build_CentralMorphism; intros.
  abstract (setoid_rewrite (fmor_preserves_id(bin_first c));
              setoid_rewrite (fmor_preserves_id(bin_first d));
              setoid_rewrite left_identity; setoid_rewrite right_identity; reflexivity).
  abstract (setoid_rewrite (fmor_preserves_id(bin_second c));
              setoid_rewrite (fmor_preserves_id(bin_second d));
              setoid_rewrite left_identity; setoid_rewrite right_identity; reflexivity).
  apply central_morphisms_compose; auto.
  Qed.


Lemma first_preserves_centrality `{C:PreMonoidalCat}{a}{b}(f:a~~{C}~~>b){c} : CentralMorphism f -> CentralMorphism (f ⋉ c).
  intro cm.
  apply Build_CentralMorphism; simpl; intros.

  set (ni_commutes (pmon_assoc_rr c c0) f) as q.
  apply iso_shift_right' in q.
  unfold fmor in q at 1; simpl in q.
  rewrite q.
  clear q.
    
  set (ni_commutes (pmon_assoc_rr c d) f) as q.
  apply iso_shift_right' in q.
  unfold fmor in q at 1; simpl in q.
  rewrite q.
  clear q.
    
  set (ni_commutes (pmon_assoc_ll b c) g) as q.
  apply symmetry in q.
  apply iso_shift_left' in q.
  rewrite q.
  clear q.

  setoid_rewrite pmon_coherent_r at 1.
  setoid_rewrite pmon_coherent_l at 1.
  setoid_rewrite juggle3.
  setoid_rewrite juggle3.
  set (@iso_comp2 _ _ _ _ _ ((pmon_assoc C b c0) c)) as q.
  setoid_rewrite q.
  clear q.
  setoid_rewrite right_identity.
  unfold fmor at 2.
  simpl.
  setoid_rewrite (centralmor_first(CentralMorphism:=cm)).

  repeat setoid_rewrite <- associativity.
  apply comp_respects.
  apply comp_respects; [ idtac | reflexivity ].
  set (ni_commutes (pmon_assoc_ll a c) g) as q.
  apply symmetry in q.
  apply iso_shift_left' in q.
  setoid_rewrite q.
  clear q.
  repeat setoid_rewrite associativity.
  setoid_rewrite pmon_coherent_l.
  set (pmon_coherent_l(PreMonoidalCat:=C) c a d) as q.
  apply isos_forward_equal_then_backward_equal in q.
  setoid_rewrite q.
  clear q.
  setoid_rewrite <- pmon_coherent_r.
  setoid_rewrite iso_comp1.
  setoid_rewrite right_identity.
  unfold fmor at 3; simpl.
  apply comp_respects; [ idtac | reflexivity ].

  set (pmon_coherent_r a c c0) as q.
  apply isos_forward_equal_then_backward_equal in q.
  setoid_rewrite iso_inv_inv in q.
  apply q.
    
  setoid_rewrite pmon_coherent_r.
  unfold iso_inv.
  simpl.
  set (@isos_forward_equal_then_backward_equal) as q.
  unfold iso_inv in q; simpl in q.
  apply q.
  apply pmon_coherent_l.

  (* *)

  set (ni_commutes (pmon_assoc_rr a c) g) as q.
  symmetry in q.
  apply iso_shift_left' in q.
  unfold fmor in q at 2.
  simpl in q.
  setoid_rewrite q.
  clear q.
  
  set (ni_commutes (pmon_assoc _ d c) f) as q.
  apply iso_shift_right' in q.
  unfold fmor in q at 1; simpl in q.
  rewrite q.
  clear q.

  set (pmon_coherent_r d a c) as q.
  apply isos_forward_equal_then_backward_equal in q.
  rewrite iso_inv_inv in q.
  unfold iso_inv in q; simpl in q.
  rewrite q.
  clear q.

  setoid_rewrite juggle3.
  setoid_rewrite (iso_comp1 ((pmon_assoc C d c) a)).
  setoid_rewrite right_identity.

  set (ni_commutes (pmon_assoc_rr b c) g) as q.
  symmetry in q.
  apply iso_shift_left' in q.
  unfold fmor in q at 2.
  simpl in q.
  setoid_rewrite q.
  clear q.
  
  set (ni_commutes (pmon_assoc _ c0 c) f) as q.
  unfold fmor in q; simpl in q.
  apply iso_shift_right' in q.
  rewrite q.
  clear q.

  set (pmon_coherent_r c0 b c) as q.
  rewrite q.
  clear q.

  setoid_rewrite juggle3.
  setoid_rewrite juggle3.
  setoid_rewrite (iso_comp1 ((pmon_assoc C c0 c) b)).
  setoid_rewrite right_identity.

  setoid_rewrite pmon_coherent_r.
  repeat setoid_rewrite associativity.
  apply comp_respects; [ reflexivity | idtac ].
  repeat setoid_rewrite <- associativity.
  apply comp_respects.
  setoid_rewrite (fmor_preserves_comp (-⋉c)).
  apply (fmor_respects (-⋉c)).
  apply centralmor_second.
  set (pmon_coherent_r d b c) as q.
  apply isos_forward_equal_then_backward_equal in q.
  rewrite iso_inv_inv in q.
  symmetry. 
  apply q.
  Qed.

Lemma second_preserves_centrality `{C:PreMonoidalCat}{a}{b}(f:a~~{C}~~>b){c} : CentralMorphism f -> CentralMorphism (c ⋊ f).
  intro cm.
  apply Build_CentralMorphism; simpl; intros.

  set (ni_commutes (pmon_assoc_ll c a) g) as q.
  symmetry in q.
  apply iso_shift_left' in q.
  unfold fmor in q at 2.
  simpl in q.
  setoid_rewrite q.
  clear q.
  
  set (ni_commutes (pmon_assoc _ c d) f) as q.
  apply symmetry in q.
  apply iso_shift_left' in q.
  unfold fmor in q at 1; simpl in q.
  rewrite q.
  clear q.

  rewrite <- pmon_coherent_l.
  setoid_rewrite <- associativity.
  setoid_rewrite juggle3.
  set (iso_comp2 ((pmon_assoc_ll c a) d)) as q.
  setoid_rewrite q.
  setoid_rewrite right_identity.
  clear q.

  set (ni_commutes (pmon_assoc_ll c b) g) as q.
  apply symmetry in q.
  apply iso_shift_left' in q.
  unfold fmor in q at 1; simpl in q.
  setoid_rewrite q.
  clear q.
  
  set (ni_commutes (pmon_assoc _ c c0) f) as q.
  unfold fmor in q; simpl in q.
  symmetry in q.
  apply iso_shift_left' in q.
  rewrite q.
  clear q.

  rewrite pmon_coherent_l.
  setoid_rewrite <- associativity.
  setoid_rewrite juggle3.
  set (iso_comp2 ((pmon_assoc _ c c0) b)) as q.
  setoid_rewrite q.
  setoid_rewrite right_identity.
  clear q.
  setoid_rewrite pmon_coherent_l.

  repeat setoid_rewrite associativity.
  apply comp_respects; [ reflexivity | idtac ].
  repeat setoid_rewrite <- associativity.
  apply comp_respects.
  setoid_rewrite (fmor_preserves_comp (c⋊-)).
  apply (fmor_respects (c⋊-)).
  apply centralmor_first.
  set (pmon_coherent_l b c d) as q.
  apply isos_forward_equal_then_backward_equal in q.
  apply q.

  (* *)
  set (ni_commutes (pmon_assoc_ll d c) f) as q.
  apply iso_shift_right' in q.
  unfold fmor in q at 1; simpl in q.
  rewrite q.
  clear q.
  
  set (ni_commutes (pmon_assoc_rr c a) g) as q.
  apply symmetry in q.
  unfold fmor in q at 2; simpl in q.
  apply iso_shift_left' in q.
  rewrite q.
  clear q.

  setoid_rewrite juggle3.
  set (pmon_coherent_r d c a) as q.
  apply isos_forward_equal_then_backward_equal in q.
  setoid_rewrite iso_inv_inv in q.
  setoid_rewrite q.
  clear q.
  setoid_rewrite <- pmon_coherent_l.
  set (iso_comp1 (((pmon_assoc_ll d c) a))) as q.
  setoid_rewrite q.
  clear q.
  setoid_rewrite right_identity.
  setoid_rewrite juggle3.
  setoid_rewrite (centralmor_second(CentralMorphism:=cm)).
  symmetry.
  apply iso_shift_left.
  setoid_rewrite pmon_coherent_r.
  set (pmon_coherent_l c d b) as q.
  apply isos_forward_equal_then_backward_equal in q.
  setoid_rewrite q.
  clear q.
  apply iso_shift_right.
  setoid_rewrite iso_inv_inv.
  repeat setoid_rewrite <- associativity.

  set (ni_commutes (pmon_assoc_ll c0 c) f) as x.
  setoid_rewrite <- pmon_coherent_l.
  symmetry in x.
  unfold fmor in x at 2; simpl in x.
  setoid_rewrite <- x.
  clear x.

  set (ni_commutes (pmon_assoc_rr c b) g) as x.
  symmetry in x.
  unfold fmor in x at 2; simpl in x.
  setoid_rewrite pmon_coherent_l.
  setoid_rewrite <- pmon_coherent_r.
  repeat setoid_rewrite associativity.
  setoid_rewrite x.
  clear x.
  setoid_rewrite <- associativity.
  setoid_rewrite juggle3.
  setoid_rewrite pmon_coherent_r.
  set (iso_comp1 ((pmon_assoc C c0 b) c)) as x.
  setoid_rewrite x.
  clear x.
  setoid_rewrite right_identity.
  reflexivity.
  Qed.

Section CenterMonoidal.

  Context `(mc:PreMonoidalCat(I:=pI)).

  Definition CenterMonoidal_Fobj : (Center mc) ×× (Center mc) -> Center mc.
    intro.
    destruct X as [a b].
    destruct a as [a apf].
    destruct b as [b bpf].
    exists (a ⊗ b); auto.
    Defined.

  Definition CenterMonoidal_F_fmor (a b:(Center mc) ×× (Center mc)) : 
    (a~~{(Center mc) ×× (Center mc)}~~>b) ->
    ((CenterMonoidal_Fobj a)~~{Center mc}~~>(CenterMonoidal_Fobj b)).
    destruct a as [[a1 a1'] [a2 a2']].
    destruct b as [[b1 b1'] [b2 b2']].
    intro f.
    destruct f as [[f1 f1'] [f2 f2']].
    simpl in *.
    unfold hom.
    simpl.
    exists (f1 ⋉ a2 >>> b1 ⋊ f2).
    apply central_morphisms_compose.
    apply first_preserves_centrality; auto.
    apply second_preserves_centrality; auto.
    Defined.

  Definition CenterMonoidal_F : Functor _ _ CenterMonoidal_Fobj.
    refine {| fmor := CenterMonoidal_F_fmor |}.
    intros.
    destruct a as [[a1 a1'] [a2 a2']].
    destruct b as [[b1 b1'] [b2 b2']].
    destruct f as [[f1 f1'] [f2 f2']].
    destruct f' as [[g1 g1'] [g2 g2']].
    simpl in *.
    destruct H.
    apply comp_respects.
    set (fmor_respects(-⋉a2)) as q; apply q; auto.
    set (fmor_respects(b1⋊-)) as q; apply q; auto.
    intros.
    destruct a as [[a1 a1'] [a2 a2']].
    simpl in *.
    setoid_rewrite (fmor_preserves_id (-⋉a2)).
    setoid_rewrite (fmor_preserves_id (a1⋊-)).
    apply left_identity.
    intros.
    destruct a as [[a1 a1'] [a2 a2']].
    destruct b as [[b1 b1'] [b2 b2']].
    destruct c as [[c1 c1'] [c2 c2']].
    destruct f as [[f1 f1'] [f2 f2']].
    destruct g as [[g1 g1'] [g2 g2']].
    simpl in *.
    setoid_rewrite juggle3.
    setoid_rewrite <- (centralmor_first(CentralMorphism:=g1')).
    setoid_rewrite <- juggle3.
    setoid_rewrite <- fmor_preserves_comp.
    reflexivity.
    Defined.

  Definition center_I : Center mc := exist _ pI I.

  Definition center_cancelr : (func_rlecnac center_I >>>> CenterMonoidal_F) <~~~> functor_id (Center mc).
    Definition center_cancelr_niso : ∀A : Center mc, CenterMonoidal_Fobj (pair_obj A center_I) ≅ A.
      intros.
      destruct A; simpl.
      set (ni_iso (pmon_cancelr mc) x) as q.
      (*refine {| iso_forward := #q ; iso_backward := iso_backward q |}.*)
      admit.
      Defined.
    refine {| ni_iso := center_cancelr_niso |}.
    admit.
    Defined.

  Definition center_cancell : (func_llecnac center_I >>>> CenterMonoidal_F) <~~~> functor_id (Center mc).
    Definition center_cancell_niso : ∀A : Center mc, CenterMonoidal_Fobj (pair_obj center_I A) ≅ A.
      admit.
      Defined.
    refine {| ni_iso := center_cancell_niso |}.
    admit.
    Defined.

  Definition center_assoc :
    ((CenterMonoidal_F **** (functor_id _)) >>>> CenterMonoidal_F)
    <~~~> func_cossa >>>> ((((functor_id _) **** CenterMonoidal_F) >>>> CenterMonoidal_F)).

    Definition center_assoc_niso : ∀A : (Center mc ×× Center mc) ×× Center mc,
      ((((CenterMonoidal_F **** (functor_id _)) >>>> CenterMonoidal_F) A))
      ≅ ((func_cossa >>>> ((((functor_id _) **** CenterMonoidal_F) >>>> CenterMonoidal_F))) A).
      admit.
      Defined.

    refine {| ni_iso := center_assoc_niso |}.
    admit.
    Defined.

  Instance CenterMonoidal : MonoidalCat _ _ CenterMonoidal_F (exist _ pI I) :=
  { mon_cancelr := center_cancelr
  ; mon_cancell := center_cancell
  ; mon_assoc   := center_assoc
  }.
    admit.
    admit.
    Defined.

End CenterMonoidal.
