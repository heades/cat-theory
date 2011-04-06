Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 1.6.2: Opposite Categories                                         *)
(******************************************************************************)

(* we don't want to register this as an instance, because it will confuse Coq *)
Definition Opposite `(C:@Category Ob Hom) : Category Ob (fun x y => Hom y x).
  intros.
  apply (Build_Category Ob (fun x y => Hom y x)) with
    (id    := fun a         => @id    _ _ C a)
    (comp  := fun a b c f g => @comp  _ _ C c b a g f)
    (eqv   := fun a b   f g => @eqv   _ _ C b a f g).

  intros; apply Build_Equivalence;
    [ unfold Reflexive;  intros; reflexivity
    | unfold Symmetric;  intros; symmetry; auto
    | unfold Transitive; intros; transitivity y; auto
    ].
  unfold Proper. intros. unfold respectful. intros. setoid_rewrite H. setoid_rewrite H0. reflexivity.
  intros; apply (@right_identity _ _ C).
  intros; apply (@left_identity _ _ C).
  intros. symmetry; apply associativity.
  Defined.
Notation "C ⁽ºᑭ⁾" := (Opposite C)  : category_scope.

(* every functor between two categories determines a functor between their opposites *)
Definition func_op `(F:Functor(c1:=c1)(c2:=c2)(fobj:=fobj)) : Functor c1⁽ºᑭ⁾ c2⁽ºᑭ⁾ fobj.
  apply (@Build_Functor _ _ c1⁽ºᑭ⁾ _ _ c2⁽ºᑭ⁾ fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

(* we could do this by simply showing that (Opposite (Opposite C)) is isomorphic to C, but Coq distinguishes between
 * two categories being *equal* versus merely isomorphic, so it's handy to be able to do this *)
Definition func_opop `{c1:Category}`{c2:Category}{fobj}(F:Functor c1⁽ºᑭ⁾ c2⁽ºᑭ⁾ fobj) : Functor c1 c2 fobj.
  apply (@Build_Functor _ _ c1 _ _ c2 fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

Definition func_op1 `{c1:Category}`{c2:Category}{fobj}(F:Functor c1⁽ºᑭ⁾ c2 fobj) : Functor c1 c2⁽ºᑭ⁾ fobj.
  apply (@Build_Functor _ _ c1 _ _ c2⁽ºᑭ⁾ fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

Definition func_op2 `{c1:Category}`{c2:Category}{fobj}(F:Functor c1 c2⁽ºᑭ⁾ fobj) : Functor c1⁽ºᑭ⁾ c2 fobj.
  apply (@Build_Functor _ _ c1⁽ºᑭ⁾ _ _ c2 fobj (fun a b f => fmor F f)).
  abstract (intros; apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H)).
  abstract (intros; apply (@fmor_preserves_id _ _ _ _ _ _ _ F a)).
  abstract (intros; apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f)).
  Defined.

