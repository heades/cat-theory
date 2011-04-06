(******************************************************************************)
(* Chapter 1.3: Categories                                                    *)
(******************************************************************************)

Generalizable All Variables.
Require Import Notations.

(* definition 1.1 *)
Class Category
( Ob               :  Type                    )
( Hom              :  Ob -> Ob -> Type        ) :=
{ hom              := Hom                                                          where "a ~> b" := (hom a b)
; ob               := Ob

; id               :  forall  a,                          a~>a
; comp             :  forall  a b c,                      a~>b -> b~>c -> a~>c     where "f >>> g" := (comp _ _ _ f g)

; eqv              :  forall  a b,   (a~>b) -> (a~>b) -> Prop                      where "f ~~ g" := (eqv _ _ f g)
; eqv_equivalence  :  forall  a b,   Equivalence (eqv a b)
; comp_respects    :  forall  a b c, Proper (eqv a b ==> eqv b c ==> eqv a c) (comp _ _ _)

; left_identity    :  forall `(f:a~>b),                       id a >>> f  ~~ f
; right_identity   :  forall `(f:a~>b),                       f  >>> id b ~~ f
; associativity    :  forall `(f:a~>b)`(g:b~>c)`(h:c~>d), (f >>> g) >>> h ~~ f >>> (g >>> h)
}.
Coercion ob      :      Category >-> Sortclass.

Notation "a ~> b"         := (@hom _ _ _ a b)                      :category_scope.
Notation "f ~~ g"         := (@eqv _ _ _ _ _ f g)                  :category_scope.
Notation "f >>> g"        := (comp _ _ _ f g)                      :category_scope.
Notation "a ~~{ C }~~> b" := (@hom _ _ C a b)       (at level 100) :category_scope.
    (* curious: I declared a Reserved Notation at the top of the file, but Coq still complains if I remove "at level 100" *)

Open Scope category_scope.

Hint Extern 3 => apply comp_respects.
Hint Extern 1 => apply left_identity.
Hint Extern 1 => apply right_identity.

Add Parametric Relation (Ob:Type)(Hom:Ob->Ob->Type)(C:Category Ob Hom)(a b:Ob) : (hom a b) (eqv a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (eqv_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (eqv_equivalence a b))
  as parametric_relation_eqv.
  Add Parametric Morphism `(c:Category Ob Hom)(a b c:Ob) : (comp a b c)
  with signature (eqv _ _ ==> eqv _ _ ==> eqv _ _) as parametric_morphism_comp.
  auto.
  Defined.

Hint Constructors Equivalence.
Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.
Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ~~ ?A) => reflexivity.
Hint Extern 6 (?X ~~ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ~~ ?Z) => match goal with [H : ?X ~~ ?Y, H' : ?Y ~~ ?Z |- ?X ~~ ?Z] => transitivity Y end.
Hint Extern 10 (?X >>> ?Y ~~ ?Z >>> ?Q) => apply comp_respects; auto.

(* handy for rewriting *)
Lemma juggle1 : forall `{C:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e), (((f>>>g)>>>h)>>>k) ~~ (f>>>(g>>>h)>>>k).
  intros; setoid_rewrite <- associativity; reflexivity.
  Defined.
Lemma juggle2 : forall `{C:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e), (f>>>(g>>>(h>>>k))) ~~ (f>>>(g>>>h)>>>k).
  intros; repeat setoid_rewrite <- associativity. reflexivity.
  Defined.
Lemma juggle3 : forall `{C:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e), ((f>>>g)>>>(h>>>k)) ~~ (f>>>(g>>>h)>>>k).
  intros; repeat setoid_rewrite <- associativity. reflexivity.
  Defined.





