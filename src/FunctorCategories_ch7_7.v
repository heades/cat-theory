Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.

(*******************************************************************************)
(* Chapter 7.5 and 7.7: Functor Categories                                     *)
(*******************************************************************************)

(* Definition 7.9 *)
Instance FunctorCategory `(C:Category)`(D:Category)
    : Category { Fobj : C->D & Functor C D Fobj } (fun F G => (projT2 F) ~~~> (projT2 G)) :=
{ id   := fun F                   => nt_id (projT2 F)
; comp := fun F G H nt_f_g nt_g_h => nt_comp nt_f_g nt_g_h
; eqv  := fun F G nt1 nt2         => forall c, (nt1 c) ~~ (nt2 c)
}.
  intros.
   (apply Build_Equivalence;
            [ unfold Reflexive; unfold respectful; simpl; intros; reflexivity
            | unfold Symmetric; unfold respectful; simpl; intros; symmetry; auto
            | unfold Transitive; unfold respectful; simpl; intros; etransitivity; [ apply H | auto ] ]).
  abstract (intros; unfold Proper; unfold respectful; simpl; intros; setoid_rewrite H0; setoid_rewrite H; reflexivity).
  abstract (intros; simpl; apply left_identity).
  abstract (intros; simpl; apply right_identity).
  abstract (intros; simpl; apply associativity).
  Defined.

(* functors compose with each other, natural transformations compose with each other -- but you can also
 * compose a functor with a natural transformation! *)
Definition LeftWhisker
  `{C:Category}`{D:Category}`{E:Category}
  {Fobj}{F:Functor C D Fobj}
  {Gobj}{G:Functor C D Gobj}
  (nat:F ~~~> G)
  {Hobj}(H:Functor D E Hobj) : ((F >>>> H) ~~~> (G >>>> H)).
  apply Build_NaturalTransformation with (nt_component:=(fun c => H \ (nat c))).
  abstract (intros;
            simpl;
            set (@nt_commutes _ _ _ _ _ _ F _ _ G nat) as nat';
            setoid_rewrite fmor_preserves_comp;
            setoid_rewrite <- nat';
            setoid_rewrite <- (fmor_preserves_comp H);
            reflexivity).
  Defined.

Definition RightWhisker
  `{C:Category}`{D:Category}`{E:Category}
  {Fobj}(F:Functor C D Fobj)
  {Gobj}{G:Functor D E Gobj}
  {Hobj}{H:Functor D E Hobj} : (G ~~~> H) -> ((F >>>> G) ~~~> (F >>>> H)).
  intro nat.
  apply Build_NaturalTransformation with (nt_component:=(fun c => (nat (F  c)))).
  abstract (intros;
            simpl;
            set (@nt_commutes _ _ _ _ _ _ G _ _ H nat) as nat';
            setoid_rewrite nat';
            reflexivity).
  Defined.

(* also sometimes called "horizontal composition" *)
Definition GodementMultiplication
  `{A:Category}`{B:Category}`{C:Category}
  {F0obj}{F0:Functor A B F0obj}
  {F1obj}{F1:Functor A B F1obj}
  {G0obj}{G0:Functor B C G0obj}
  {G1obj}{G1:Functor B C G1obj}
  : (F0~~~>F1) -> (G0~~~>G1) -> ((F0 >>>> G0)~~~>(F1 >>>> G1)).
  intro phi.
  intro psi.
  apply Build_NaturalTransformation with (nt_component:=(fun (a:A) => G0 \ (phi a) >>> psi (F1 a))).
  abstract (intros;
            set (@nt_commutes _ _ _ _ _ _ F0 _ _ F1 phi) as comm1;
            set (@nt_commutes _ _ _ _ _ _ G0 _ _ G1 psi) as comm2;
            setoid_rewrite <- comm2;
            simpl;
            setoid_rewrite associativity;
            setoid_rewrite fmor_preserves_comp;
            setoid_rewrite comm1;
            setoid_rewrite <- fmor_preserves_comp;
            repeat setoid_rewrite <- associativity;
            apply comp_respects; try reflexivity;
            setoid_rewrite comm2;
            reflexivity).
  Defined.
  (* this operation is also a bifunctor from (FunctorCategory A B)*(FunctorCategory B C) to (FunctorCategory A C);
   * it is functorial *)

