(*******************************************************************************)
(* Hughes Arrows                                                               *)
(*******************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import EpicMonic_ch2_1.
Require Import InitialTerminal_ch2_2.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import Coherence_ch7_8.
Require Import MonoidalCategories_ch7_8.
Require Import FreydCategories.
Require Import CoqCategory.

(* these notations are more for printing back than writing input (helps coax Coq into better pretty-printing) *)
Notation "'_swap'"  := (fun xy => let (a0, b0) := xy in ⟨b0, a0 ⟩).
Notation "'_assoc'" := (fun xyz => let (ab, c) := xyz in let (a0, b0) := ab in ⟨a0, ⟨b0, c ⟩ ⟩).

Class Arrow
( arr_hom'            :  Type->Type->Type      ) :=
{ arr_hom             := arr_hom' (* hack to make Coq notations work *)     where "a ~> b" := (arr_hom a b)   

; arr_arr             :  forall {a b},      (a->b) -> a~>b
; arr_comp            :  forall {a b c},     a~>b  -> b~>c -> a~>c          where "f >>> g" := (arr_comp f g)
; arr_first           :  forall {a b} c,     a~>b  -> (a*c)~>(b*c)          where "f ⋊  d"  := (arr_first d f)

; arr_eqv             :  forall {a b},           (a~>b) -> (a~>b) -> Prop   where "a ~~ b"  := (arr_eqv a b)
; arr_eqv_equivalence :  forall {a b},           Equivalence (@arr_eqv a b)

; arr_comp_respects   :  forall {a b c},         Proper (arr_eqv ==> arr_eqv ==> arr_eqv)  (@arr_comp  a b c)
; arr_first_respects  :  forall {a b c},         Proper (arr_eqv ==> arr_eqv)              (@arr_first a b c)
; arr_arr_respects    :  forall {a b}(f g:a->b), Proper (extensionality a b ==> arr_eqv)   (@arr_arr   a b)

; arr_left_identity   :  forall `(f:a~>b),                    (arr_arr (fun x => x)) >>> f ~~ f
; arr_right_identity  :  forall `(f:a~>b),                    f >>> (arr_arr (fun x => x)) ~~ f
; arr_associativity   :  forall `(f:a~>b)`(g:b~>c)`(h:c~>d),               (f >>> g) >>> h ~~ f >>> (g >>> h)
; arr_comp_preserves  :  forall `(f:a->b)`(g:b->c),                        arr_arr (g ○ f) ~~ arr_arr f >>> arr_arr g
; arr_extension       :  forall a b (f:a->b), forall d,                    (arr_arr f) ⋊ d ~~ arr_arr (Λ⟨x,y⟩ ⟨f x,y⟩)
; arr_first_preserves :  forall {d}`(f:a~>b)`(g:b~>c),                       (f >>> g) ⋊ d ~~ f ⋊ d >>> g ⋊ d
; arr_exchange        :  forall `(f:a~>b)`(g:c->d),     arr_arr (Λ⟨x,y⟩ ⟨x,g y⟩) >>> f ⋊ _ ~~ f ⋊ _ >>> arr_arr (Λ⟨x,y⟩ ⟨x,g y⟩)
; arr_unit            :  forall {c}`(f:a~>b),                  f ⋊ c >>> arr_arr (Λ⟨x,y⟩x) ~~ (arr_arr (Λ⟨x,y⟩x)) >>> f
; arr_association     :  forall {c}{d}`(f:a~>b), (f⋊c)⋊d >>> arr_arr(Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩) ~~ arr_arr (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩) >>> f⋊_
}.

(*
  ; loop : forall {a}{b}{c}, (a⊗c~>b⊗c) -> (a~>b)
  (* names taken from Figure 7 of Paterson's "A New Notation for Arrows", which match the CCA paper *)
  ; left_tightening  : forall {a}{b}{c}{f:a⊗b~>c⊗b}{h},         loop (first c a b h >>> f) ~~ h >>> loop f
  ; right_tightening : forall {a}{b}{c}{f:a⊗b~>c⊗b}{h},         loop (f >>> first c a b h) ~~ loop f >>> h
  ; sliding          : forall {a}{b}{c}{f:a⊗c~>b⊗c}{k}, central k -> loop (f >>> second _ _ b k) ~~ loop (second _ _ a k >>> f)
  ; vanishing        : forall {a}{b}{c}{d}{f:(a⊗c)⊗d~>(b⊗c)⊗d},            loop (loop f) ~~ loop (#assoc⁻¹ >>> f >>> #assoc)
  ; superposing      : forall {a}{b}{c}{d}{f:a⊗c~>b⊗c},   second _ _ d (loop f) ~~ loop (#assoc  >>> second _ _ d f >>> #assoc⁻¹)
*)

(* register the arrow equivalence relation as a rewritable setoid, with >>> and first as morphisms *)
Add Parametric Relation `(ba:Arrow)(a b:Type) : (arr_hom a b) arr_eqv 
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (@arr_eqv_equivalence _ _ a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (@arr_eqv_equivalence _ _ a b))
  transitivity proved by (@Equivalence_Transitive _ _ (@arr_eqv_equivalence _ _ a b))
  as parametric_relation_arr_eqv.
  Add Parametric Morphism `(ba:Arrow)(a b c:Type) : (@arr_comp _ _ a b c)
  with signature (arr_eqv ==> arr_eqv ==> arr_eqv) as parametric_morphism_arr_comp.
  intros; apply arr_comp_respects; auto.
  Defined.
  Add Parametric Morphism `(ba:Arrow)(a b c:Type) : (@arr_first _ _ a b c)
  with signature (arr_eqv ==> arr_eqv) as parametric_morphism_arr_first.
  intros; apply arr_first_respects; auto.
  Defined.

Notation "a ~> b"  := (arr_hom a b)   :arrow_scope.
Notation "f >>> g" := (arr_comp f g)  :arrow_scope.
Notation "f ⋊  d"  := (arr_first d f) :arrow_scope.
Notation "a ~~ b"  := (arr_eqv a b)   :arrow_scope.

Open Scope arrow_scope.

(* Formalized Definition 2.3 *)
Class BiArrow
( biarr_hom   :  Type -> Type -> Type            ) :=
{ biarr_super :> Arrow biarr_hom

; biarr_biarr :  forall {a b},            (a->b) -> (b->a) -> (a~>b)   where "f <--> g" := (biarr_biarr g f)
; biarr_inv   :  forall {a b},              a~>b -> b~>a               where "! f"      := (biarr_inv f)

(* BiArrow laws are numbered based on section 5 of Hunen+Jacobs paper *)
; biarr_law3' :  forall {a}{b}{c}{f1}{f2:b->c}{g1}{c2:a->b},           f1<-->c2 >>> g1<-->f2 ~~ (f1 ○ g1) <--> (f2 ○ c2)
; biarr_law4' :  forall {a}{b}{f:a~>b},                       (fun x=>x)<-->(fun x=>x) >>> f ~~ f
; biarr_law4'':  forall {a}{b}{f:a~>b},                 f >>> (fun x=>x)<-->(fun x=>x)       ~~ f
; biarr_law8' :  forall {a}{b}{f:a->b}{g}{c},                                   (f<-->g) ⋊ c ~~ (Λ⟨x,y⟩ ⟨f x,y⟩)<-->(Λ⟨x,y⟩ ⟨g x,y⟩)
; biarr_law22 :  forall {a}{b}{f:a~>b},                                                !(!f) ~~ f
; biarr_law23 :  forall {a}{b}{c}{f:b~>c}{g:a~>b},                                !(g >>> f) ~~ !f >>> !g
; biarr_law24 :  forall {a}{b}{f:a->b}{g},                                         !(f<-->g) ~~ g<-->f
; biarr_law25 :  forall {a}{b}{f:a~>b}{c},                                          !(f ⋊ _) ~~ (!f) ⋊ c
; biarr_law6' :  forall {a}{b}{c}{d}{f:a->b}{g}{h:c~>d},  (h ⋊ _) >>> (Λ⟨x,y⟩ ⟨x,f y⟩)<-->(Λ⟨x,y⟩ ⟨x,g y⟩) ~~
                                                                     (Λ⟨x,y⟩ ⟨x,f y⟩)<-->(Λ⟨x,y⟩ ⟨x,g y⟩) >>> (h ⋊ _)

(* for complete example, we'd also need biarr_biarr_respects and biarr_inv_respects, but this paper isn't about BiArrows *)
}.

Notation "f <--> g" := (biarr_biarr g f) :biarrow_scope.
Notation "! f"      := (biarr_inv     f) :biarrow_scope.

Open Scope biarrow_scope.
Inductive left_invertible  `{ba:BiArrow}{a}{b}(f:a~>b) : Prop := LI : ((f >>> !f) ~~ (arr_arr (fun x=>x))) -> left_invertible f.
Inductive right_invertible `{ba:BiArrow}{a}{b}(f:a~>b) : Prop := RI : ((!f >>> f) ~~ (arr_arr (fun x=>x))) -> right_invertible f.
Close Scope biarrow_scope.

Hint Extern 4 (?A ~~ ?A) => reflexivity.
Hint Extern 6 (?X ~~ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ~~ ?Z) => match goal with [H : ?X ~~ ?Y, H' : ?Y ~~ ?Z |- ?X ~~ ?Z] => transitivity Y end.
Hint Extern 10 (?X >>> ?Y ~~ ?Z >>> ?Q) => apply arr_comp_respects; auto.
Hint Constructors Arrow.

(* Formalized Lemma 3.2 *)
Definition arrows_are_categories : forall `(ba:Arrow), Category Type arr_hom.
  intros.
  refine
    {| id   := fun a         => arr_arr (fun x => x)
     ; comp := fun a b c f g => arr_comp f g
     ; eqv  := fun a b f g   => arr_eqv f g    |}; intros; auto.
  apply arr_left_identity.
  apply arr_right_identity.
  apply arr_associativity.
  Defined.
Coercion arrows_are_categories : Arrow >-> Category.

(* a tactic to throw the kitchen sink at Arrow goals; using ATBR (http://coq.inria.fr/contribs/ATBR.html) would be a better idea *)
Ltac magic :=
  repeat apply arr_comp;
  repeat apply arr_first;
  repeat apply arr_arr_respects;
  repeat setoid_rewrite arr_left_identity;
  repeat setoid_rewrite arr_right_identity;
  repeat setoid_rewrite <- arr_comp_preserves;
  repeat setoid_rewrite arr_extension;
  repeat setoid_rewrite arr_first_preserves.
  (* need to handle associat, exchange, unit, association *)

Definition Arrows_are_Binoidal `(ba:Arrow) : BinoidalCat ((arrows_are_categories ba)) prod.
    intros; apply Build_BinoidalCat; intros;
    [ apply (Build_Functor _ _ (ba) _ _ (ba) (fun X => X*a)
            (fun X Y f => (arr_first(Arrow:=ba)) a f))
    | apply (Build_Functor _ _ (ba) _ _ (ba) (fun X => a*X) 
            (fun X Y f => arr_arr (Λ⟨x,y⟩ ⟨y,x⟩) >>> arr_first(Arrow:=ba) a f >>> arr_arr(Arrow:=ba) (Λ⟨x,y⟩ ⟨y,x⟩)))
    ]; intros; simpl; intros;
    [ apply arr_first_respects; auto
    | setoid_rewrite arr_extension; repeat setoid_rewrite <- arr_comp_preserves; apply arr_arr_respects
    | symmetry; apply arr_first_preserves
    | repeat apply arr_comp_respects; try reflexivity
    | setoid_rewrite arr_extension; repeat setoid_rewrite <- arr_comp_preserves
    | setoid_rewrite arr_first_preserves
    ]; intros; auto.
    idtac.
    unfold extensionality; intros; destruct x; auto.
    simpl in H; setoid_rewrite H; auto.
    apply arr_arr_respects; intros; auto.
    unfold extensionality; intros; destruct x; auto.
    repeat rewrite arr_associativity; repeat setoid_rewrite <- arr_comp_preserves.
    apply arr_comp_respects; try reflexivity.
    apply arr_comp_respects; try reflexivity.
    setoid_rewrite <- arr_associativity.
    repeat setoid_rewrite <- arr_comp_preserves.
    setoid_rewrite <- arr_associativity.
    apply arr_comp_respects; try reflexivity.
    transitivity (arr_comp ((arr_arr(Arrow:=ba)) (fun x=>x)) (arr_first(Arrow:=ba) a g)).
    apply arr_comp_respects; try reflexivity.
    apply arr_arr_respects; intros; auto; unfold extensionality; intros; auto; try destruct x; auto.
    apply arr_left_identity.
    Defined.

  Definition arrow_cancelr_iso : forall `(ba:Arrow)(A:ba), (Isomorphic(C:=ba)) (A*Datatypes.unit) A.
    intros; apply (Build_Isomorphic _ _ ba (A*Datatypes.unit) A (arr_arr (Λ⟨x,y⟩ x))  (arr_arr (fun x => ⟨x,tt⟩))).
    simpl; setoid_rewrite <- arr_comp_preserves; apply arr_arr_respects.
    intros; destruct X. auto. auto.
    unfold extensionality; intros; simpl. destruct x. destruct u. auto.
    simpl; setoid_rewrite <- arr_comp_preserves; reflexivity.
    Defined.
  Definition arrow_cancelr_ni_iso `(ba:Arrow)
    : (((bin_first(BinoidalCat:=Arrows_are_Binoidal ba)) (Datatypes.unit)) <~~~> functor_id (ba)).
    intros; eapply Build_NaturalIsomorphism.
    instantiate (1:=arrow_cancelr_iso ba).
    intros;
      transitivity (
        arr_comp(Arrow:=ba)
        (fmor (bin_first(BinoidalCat:=Arrows_are_Binoidal ba) Datatypes.unit) f)
        (arr_arr(Arrow:=ba) (fun xy : B * unit => let (a, b) := xy in (fun (x : B) (_ : unit) => x) a b))
      ).
    symmetry.
    apply (arr_unit(Arrow:=ba)(c:=(Datatypes.unit)) f).
    apply Equivalence_Reflexive.
    Defined.
  Definition arrow_cancell_iso `(ba:Arrow)
    : forall (A:ba), (Isomorphic(C:=ba))  (Datatypes.unit*A) A.
    intros; apply (Build_Isomorphic _ _ ba _ _ (arr_arr (Λ⟨x,y⟩ y)) (arr_arr (fun x => ⟨tt,x⟩))).
    simpl; setoid_rewrite <- arr_comp_preserves; apply arr_arr_respects.
    intros; destruct X. auto. auto.
    unfold extensionality; intros; simpl. destruct x. auto. destruct u. auto.
    simpl; setoid_rewrite <- arr_comp_preserves; reflexivity.
    Defined.
  Definition arrow_cancell_ni_iso `(ba:Arrow)
    : (((bin_second(BinoidalCat:=(Arrows_are_Binoidal ba))) (Datatypes.unit)) <~~~> functor_id (ba)).
    intros; eapply Build_NaturalIsomorphism.
    instantiate (1:=arrow_cancell_iso ba).
    intros. simpl.
    repeat setoid_rewrite arr_associativity.
      setoid_rewrite <- arr_comp_preserves.
      simpl;
        setoid_replace (arr_arr (fun x : B * unit => let (_, b) := let (a, b) := x in ⟨b, a ⟩ in b))
        with (arr_arr (fun x : B * unit => let (b, _) := x in b)).
      setoid_rewrite arr_unit.
      setoid_rewrite <- arr_associativity.
      magic.
      apply arr_comp_respects.
      apply arr_arr_respects.
      intros; destruct X; auto.
      intros; destruct X; auto.
      unfold extensionality; intros; simpl.
      destruct x; auto.
      apply Equivalence_Reflexive.
      apply arr_arr_respects.
      intros; destruct X; auto.
      intros; destruct X; auto.
      unfold extensionality; intros; simpl.
      destruct x.
      auto.
   Defined.

  Definition arrow_assoc_iso `(ba:Arrow) : forall A B C, (Isomorphic(C:=ba)) ((A*B)*C) (A*(B*C)).
    intros; eapply (Build_Isomorphic _ _ ba _ _ (arr_arr (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩)) (arr_arr (Λ⟨x,⟨y,z⟩⟩ ⟨⟨x,y⟩,z⟩)));
    [ intros; simpl; setoid_rewrite <- arr_comp_preserves
    | intros; simpl; simpl; setoid_rewrite <- arr_comp_preserves; apply arr_arr_respects; auto
    ]; simpl; try apply arr_arr_respects; intros; try destruct X; try destruct x; try destruct p; auto;
    unfold extensionality; intros; intros; destruct x; destruct p; auto.
    Defined.
  Definition arrow_assoc_ni_iso `(ba:Arrow) : 
  (∀A : ba, ∀B : ba,
    (bin_second(BinoidalCat:=(Arrows_are_Binoidal ba))) A >>>>
    (bin_first(BinoidalCat:=(Arrows_are_Binoidal ba))) B <~~~>
    (bin_first(BinoidalCat:=(Arrows_are_Binoidal ba))) B >>>>
    (bin_second(BinoidalCat:=(Arrows_are_Binoidal ba))) A).
  intros.
  eapply Build_NaturalIsomorphism.
  instantiate (1:=(fun X:ba => (arrow_assoc_iso ba A X B))).
  simpl; intros.
  setoid_rewrite arr_first_preserves.
  setoid_rewrite arr_first_preserves.
  setoid_rewrite arr_associativity.
  setoid_replace
    ( (arr_first(Arrow:=ba) A (arr_first(Arrow:=ba) B f)) >>> @arr_arr arr_hom' ba (B0 * B * A) (A * (B0 * B)) _swap)
    with
      ((( (arr_first(Arrow:=ba) A (arr_first(Arrow:=ba) B f)) >>> 
      (arr_arr (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩))) >>> (arr_arr (Λ⟨x,⟨y,z⟩⟩ ⟨⟨x,y⟩,z⟩))) >>> 
      @arr_arr arr_hom' ba (B0 * B * A) (A * (B0 * B)) _swap).
  setoid_rewrite arr_association.
  repeat setoid_rewrite arr_associativity.
  setoid_replace
    ((arr_first(Arrow:=ba) B (arr_first(Arrow:=ba) A f))
      >>> ((arr_first(Arrow:=ba) B (@arr_arr arr_hom' ba (B0 * A) (A * B0) _swap))
        >>> (@arr_arr arr_hom' ba (A * B0 * B) (A * (B0 * B)) _assoc)))
    with
    ((((arr_first(Arrow:=ba) B (arr_first(Arrow:=ba) A f))
        >>> (arr_arr (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩)))
    >>> (arr_arr (Λ⟨x,y⟩ ⟨y,x⟩))
    >>> (arr_arr (Λ⟨x,y⟩ ⟨y,x⟩))
    >>> (arr_arr (Λ⟨x,⟨y,z⟩⟩ ⟨⟨x,y⟩,z⟩)))
      >>> ((arr_first(Arrow:=ba) B (@arr_arr arr_hom' ba (B0 * A) (A * B0) _swap))
        >>> (@arr_arr arr_hom' ba (A * B0 * B) (A * (B0 * B)) _assoc))).
  setoid_rewrite arr_association.
  setoid_replace (arr_first(Arrow:=ba) (A*B) f)
    with (((arr_first(Arrow:=ba) (A*B) f)
      >>> (arr_arr (Λ⟨x,y⟩ ⟨x,(fun q => match q with (a,b) => (b,a) end) y⟩)))
      >>> (arr_arr (Λ⟨x,y⟩ ⟨x,(fun q => match q with (a,b) => (b,a) end) y⟩))).
  setoid_rewrite <- arr_exchange.
  repeat magic.
  repeat setoid_rewrite <- arr_associativity.
  repeat magic.
  repeat setoid_rewrite arr_associativity.
  repeat magic.
  apply arr_comp_respects.
  apply arr_arr_respects.
  intros; destruct X; destruct p; auto.
  intros; destruct X; destruct p; auto.
  unfold extensionality; intros; simpl.
  destruct x. destruct p; auto.
  apply arr_comp_respects.
  reflexivity.
  apply arr_arr_respects.
  intros; destruct X; destruct p; auto.
  intros; destruct X; destruct p; auto.
  unfold extensionality; intros; simpl.
  destruct x. destruct p; auto.
  setoid_rewrite arr_associativity.
  magic.
  setoid_replace (arr_first(Arrow:=ba) (A*B) f) with (arr_first(Arrow:=ba) (A*B) f >>> arr_arr (fun x => x)).
  apply arr_comp_respects.
  setoid_rewrite arr_right_identity.
  reflexivity.
  apply arr_arr_respects.
  intros; destruct X; destruct p; auto.
  intros; destruct X; destruct p; auto.
  unfold extensionality; intros; simpl.
  destruct x. destruct p; auto.
  setoid_rewrite <-  arr_right_identity.
  setoid_rewrite arr_associativity.
  repeat magic.
  reflexivity.
  repeat magic.
  repeat setoid_rewrite arr_associativity.
  repeat magic.
  apply arr_comp_respects.
  reflexivity.
  apply arr_arr_respects.
  intros; destruct X; destruct p; auto.
  intros; destruct X; destruct p; auto.
  unfold extensionality; intros; simpl.
  destruct x. destruct p; auto.
  repeat setoid_rewrite arr_associativity.
  repeat magic.
  apply arr_comp_respects.
  reflexivity.
  apply arr_arr_respects.
  intros; destruct X; destruct p; auto.
  intros; destruct X; destruct p; auto.
  unfold extensionality; intros; simpl.
  destruct x. destruct p; auto.
  Defined.

  Definition arrow_assoc_rr_iso `(ba:Arrow) := fun a b X:ba => iso_inv _ _ (arrow_assoc_iso ba X a b).
  Definition arrow_assoc_rr_ni_iso `(ba:Arrow) : 
    ∀a b:ba, NaturalIsomorphism
    (bin_first(BinoidalCat:=(Arrows_are_Binoidal ba)) ((bin_obj(BinoidalCat:=(Arrows_are_Binoidal ba))) a b))
    ((bin_first(BinoidalCat:=(Arrows_are_Binoidal ba)) a)
      >>>>
      (bin_first(BinoidalCat:=(Arrows_are_Binoidal ba)) b)).
    intros; eapply Build_NaturalIsomorphism.
    instantiate(1:=arrow_assoc_rr_iso ba a b).
    intros.
    simpl.
    setoid_replace ((arr_first(Arrow:=ba) (a*b) f))
      with (arr_arr (fun q:A*(a*b) => (Λ⟨x,⟨y,z⟩⟩ ⟨⟨x,y⟩,z⟩) q)
        >>> ((arr_arr (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩))
        >>> (arr_first(Arrow:=ba) (a*b) f))).
    setoid_rewrite <- arr_association.
    repeat setoid_rewrite arr_associativity.
    magic.
    apply arr_comp_respects.
    apply arr_arr_respects.
    intros. destruct X. destruct p. auto.
    intros. destruct X. destruct p. auto.
    unfold extensionality.
    intros; auto.
    transitivity (arr_first(Arrow:=ba) b (arr_first(Arrow:=ba) a f) >>> arr_arr (fun x=>x)).
    setoid_rewrite arr_right_identity.
    reflexivity.
    apply arr_comp_respects.
    reflexivity.
    apply arr_arr_respects.
    intros. destruct X. destruct p. auto.
    intros. destruct X. destruct p. auto.
    unfold extensionality.
    intros; auto.
    destruct x.
    destruct p.
    auto.
    setoid_rewrite <- arr_associativity.
    magic.
    transitivity (arr_arr (fun x=>x) >>> (arr_first(Arrow:=ba) (a*b) f)).
    setoid_rewrite arr_left_identity.
    reflexivity.
    apply arr_comp_respects.
    apply arr_arr_respects.
    intros. destruct X. destruct p. auto.
    intros. destruct X. destruct p. auto.
    unfold extensionality.
    intros; auto.
    destruct x.
    destruct p.
    auto.
    reflexivity.
    Defined.

  Definition arrow_assoc_ll_iso `(ba:Arrow) := fun a b X:ba => arrow_assoc_iso ba a b X.
  Definition arrow_assoc_ll_ni_iso `(ba:Arrow) : 
  forall a b:ba, NaturalIsomorphism
    (bin_second(BinoidalCat:=(Arrows_are_Binoidal ba)) ((bin_obj(BinoidalCat:=(Arrows_are_Binoidal ba))) a b))
    ((bin_second(BinoidalCat:=(Arrows_are_Binoidal ba)) b)
      >>>>
      (bin_second(BinoidalCat:=(Arrows_are_Binoidal ba)) a)).
  intros. 
  eapply Build_NaturalIsomorphism.
  simpl; intros.
  instantiate(1:=(arrow_assoc_ll_iso ba a b)).
  simpl.
  magic.
  repeat setoid_rewrite arr_associativity.
  setoid_replace
    ((arr_first a (arr_first(Arrow:=ba) b f)) >>> ((arr_first _ ((@arr_arr arr_hom' ba (B * b) (b * B) _swap))) >>>
       @arr_arr arr_hom' ba (b * B * a) (a * (b * B)) _swap))
    with
      ((((arr_first a (arr_first(Arrow:=ba) b f)
        >>> ((arr_arr(a:=((B*b)*a)) (Λ⟨⟨x,y⟩,z⟩ ⟨x,⟨y,z⟩⟩)))))
      >>> (arr_arr(Arrow:=ba) (Λ⟨x,yz⟩ ⟨x,(match yz with (y,z) => (z,y) end)⟩)))
      >>> (arr_arr(Arrow:=ba) (Λ⟨x,⟨y,z⟩⟩ ⟨y,⟨z,x⟩⟩))).
  setoid_rewrite arr_association.
  setoid_replace (arr_arr(a:=((A*b)*a)) _assoc >>> (arr_first(Arrow:=ba) (b*a) f) >>>
       arr_arr(Arrow:=ba)
         (fun xy : B * (b * a) =>
          let (a0, b0) := xy in ⟨a0, let (y, z) := b0 in ⟨z, y ⟩ ⟩))
  with
    (arr_arr(a:=((A*b)*a)) _assoc >>> ((arr_first(Arrow:=ba) (b*a) f) >>>
      arr_arr(Arrow:=ba)
      (fun xy : B * (b * a) =>
          let (a0, b0) := xy in ⟨a0, ((fun xy:b*a => let (a0, b0) := xy in ⟨b0, a0 ⟩)) b0 ⟩))).
  setoid_rewrite <- arr_exchange.
  repeat magic.
  repeat setoid_rewrite <- arr_associativity.
  repeat magic.
  apply arr_comp_respects.
  apply arr_comp_respects.
  apply arr_arr_respects.
  exact (fun xyz => match xyz with (xy,z) => match xy with (x,y) => (z,(x,y)) end end).
  exact (fun xyz => match xyz with (xy,z) => match xy with (x,y) => (z,(x,y)) end end).
  unfold extensionality; intros; simpl.
  destruct x.
  destruct b0.
  auto.
  reflexivity.
  apply arr_arr_respects.
  intros. destruct X. destruct b1. auto.
  intros. destruct X. destruct b1. auto.
  unfold extensionality; intros; simpl.
  destruct x.
  destruct b1.
  auto.
  repeat setoid_rewrite <- arr_associativity.
  apply arr_comp_respects.
  reflexivity.
  apply arr_arr_respects.
  intros. destruct X. destruct p. auto.
  intros. destruct X. destruct p. auto.
  unfold extensionality; intros; simpl.
  destruct x.
  destruct p.
  auto.
  setoid_rewrite arr_extension.
  repeat setoid_rewrite arr_associativity.
  magic.
  apply arr_comp_respects.
  reflexivity.
  apply arr_arr_respects.
  intros. destruct X. destruct p. auto.
  intros. destruct X. destruct p. auto.
  unfold extensionality; intros; simpl.
  destruct x.
  destruct p.
  auto.
  Defined.

  Instance arrows_monoidal `(ba:Arrow) : PreMonoidalCat (Arrows_are_Binoidal ba) (Datatypes.unit) :=
  { pmon_assoc    := arrow_assoc_ni_iso ba
  ; pmon_cancelr  := arrow_cancelr_ni_iso ba
  ; pmon_cancell  := arrow_cancell_ni_iso ba
  ; pmon_assoc_ll := arrow_assoc_ll_ni_iso ba
  ; pmon_assoc_rr := arrow_assoc_rr_ni_iso ba
  }.
  apply Build_Pentagon; intros.
  intros; simpl.
    repeat setoid_rewrite arr_extension.
    repeat setoid_rewrite <- arr_comp_preserves.
    apply arr_arr_respects; unfold extensionality; intros; simpl;
      try destruct x; try destruct X; try destruct b0; try destruct p; auto.
      destruct b0. unfold bin_obj. auto.
      destruct b0. unfold bin_obj. auto.
      destruct b0. unfold bin_obj. auto.
  apply Build_Triangle; intros; simpl.
    repeat setoid_rewrite arr_extension.
    repeat setoid_rewrite <- arr_comp_preserves.
    apply arr_arr_respects; unfold extensionality; intros; simpl;
      try destruct x; try destruct X; try destruct p; try destruct b0; try destruct p; unfold bin_obj; auto.
  simpl. apply arr_arr_respects;
  [ exact (fun (xy:unit*unit) => tt)
  | exact (fun (xy:unit*unit) => tt)
  | idtac
  ]; unfold extensionality; intros; simpl; destruct x; destruct u; destruct u0; auto.
  intros; reflexivity.
  intros; reflexivity.
  Defined.

Definition arrow_inclusion_functor `(ba:Arrow) : Functor coqCategory (ba) (fun x=>x).
  intros; apply (Build_Functor _ _ coqCategory _ _ (ba) _ (fun A B => fun f:A->B => arr_arr f));
   intros; unfold eqv; simpl;
    [ apply arr_arr_respects; auto
    | reflexivity
    | symmetry; apply arr_comp_preserves ].
  Defined.

Instance Arrow_inclusion_is_a_monoidal_functor `(ba:Arrow)
: PreMonoidalFunctor coqPreMonoidalCat (arrows_monoidal ba) (fun x=>x) :=
{ mf_F := arrow_inclusion_functor ba
}.
  simpl; apply iso_id.
  intros; apply (Build_NaturalIsomorphism _ _ coqCategory _ _ (ba) (fun a0 : Type => a0 * a) (fun a0 : Type => a0 * a) _ _ 
         (fun A:coqCategory => (iso_id(C:=ba)) ((fun a0 : Type => a0 * a) A))).
  intros; simpl; setoid_rewrite ((arr_extension(Arrow:=ba)) A B f a); setoid_rewrite <- arr_comp_preserves; reflexivity.
  intros; apply (@Build_NaturalIsomorphism _ _ coqCategory _ _ (ba) (fun a0 : Type => a * a0) (fun a0 : Type => a * a0) _ _ 
         (fun A:coqCategory => (iso_id(C:=ba)) ((fun a0 : Type => a * a0) A))).
  intros; simpl; setoid_rewrite arr_extension; repeat setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; intros; unfold extensionality; intros; try destruct X; try destruct x; try destruct p; auto.
  intros.
  intros; apply Build_CentralMorphism; intros. simpl.

  simpl.
  setoid_rewrite arr_extension.
  setoid_rewrite <- arr_associativity.
  setoid_rewrite <- arr_associativity.
  repeat setoid_rewrite <- arr_comp_preserves.
  transitivity (
    arr_arr (fun x:a*c => let (a0,c0) := x in (c0,a0))
    >>>
    arr_arr (fun x:c*a => let (c0,a0) := x in (c0, f a0)) >>> ((arr_first(Arrow:=ba)) b g) >>>
    (arr_arr (fun x:d*b => let (d0,b0):=x in (b0,d0)))).
  repeat setoid_rewrite <- arr_associativity.
  apply arr_comp_respects; try reflexivity.
  apply arr_comp_respects; try reflexivity.
  repeat setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; unfold extensionality; intros; try destruct X; try destruct x; intros; auto.
  repeat setoid_rewrite arr_associativity.
  apply arr_comp_respects; try reflexivity.
  repeat setoid_rewrite <- arr_associativity.
  setoid_rewrite <- arr_extension.
  setoid_rewrite arr_extension.
  repeat setoid_rewrite arr_associativity.
  repeat setoid_rewrite <- arr_comp_preserves.
  repeat setoid_rewrite <- arr_associativity.
  setoid_rewrite arr_exchange.
  repeat setoid_rewrite arr_associativity.
  apply arr_comp_respects; try reflexivity.
  repeat setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; unfold extensionality; intros; try destruct X; try destruct x; intros; auto.

  simpl.
  setoid_rewrite arr_extension.
  setoid_rewrite <- arr_associativity.
  setoid_rewrite <- arr_associativity.
  repeat setoid_rewrite <- arr_comp_preserves.
  transitivity (arr_arr (fun x:c*a => let (c0,a0) := x in (c0, f a0)) >>> ((arr_first(Arrow:=ba)) b g)).
  setoid_rewrite arr_exchange.
  repeat setoid_rewrite arr_associativity.
  apply arr_comp_respects. reflexivity.
  repeat setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; unfold extensionality; intros; try destruct X; try destruct x; intros; auto.
  apply arr_comp_respects; try reflexivity.
  apply arr_arr_respects; unfold extensionality; intros; try destruct X; try destruct x; intros; auto.
  Defined.

Definition arrow_swap_iso `(ba:Arrow) : forall A B, (Isomorphic(C:=ba)) (A*B) (B*A).
  intros; apply (Build_Isomorphic _ _ ba _ _ (arr_arr (Λ⟨x,y⟩ ⟨y,x⟩)) (arr_arr (Λ⟨x,y⟩ ⟨y,x⟩)));
  simpl; setoid_rewrite <- arr_comp_preserves;
  apply arr_arr_respects;
  intros; auto; intros; auto;
  unfold extensionality; intros; simpl.
  try destruct X; try destruct x; auto; destruct x; auto.
  destruct x. simpl. reflexivity.
  Defined.

Instance arrows_are_braided `(ba:Arrow) : BraidedCat (arrows_monoidal ba).
  intros; apply (Build_BraidedCat _ _ (ba) _ _ _ _ (fun A B => arrow_swap_iso ba A B));
    intros; simpl;
      repeat setoid_rewrite arr_extension;
        repeat setoid_rewrite <- arr_associativity;
          repeat setoid_rewrite <- arr_comp_preserves;
            apply arr_arr_respects; intros; simpl; try destruct X; auto; unfold extensionality; unfold bin_obj;
              intros; auto; try destruct x; try destruct p; try destruct b0; auto.
  Defined.

Instance arrows_are_symmetric `(ba:Arrow) : SymmetricCat (arrows_are_braided ba).
  intros; apply Build_SymmetricCat; intros. simpl. reflexivity.
  Defined.

Instance Freyd_from_Arrow `(ba:Arrow) 
: FreydCategory coqPreMonoidalCat :=
{ freyd_C_cartesian   := coqCartesianCat
; freyd_K             := ba
; freyd_K_binoidal    := Arrows_are_Binoidal ba
; freyd_K_monoidal    := arrows_monoidal ba
; freyd_F             := Arrow_inclusion_is_a_monoidal_functor ba
; freyd_K_braided     := arrows_are_braided ba
; freyd_K_symmetric   := arrows_are_symmetric ba
}.
  intros; apply Build_CentralMorphism; intros; simpl.
  repeat setoid_rewrite arr_extension.
  repeat setoid_rewrite <- arr_associativity.
  repeat setoid_rewrite <- arr_comp_preserves.
  setoid_replace
    (arr_arr (fun x : a * c => let (a0, b0) := let (a0, b0) := x in ⟨f a0, b0 ⟩ in ⟨b0, a0 ⟩) >>> (arr_first(Arrow:=ba) b g))
      with
    (arr_arr (fun x : a * c => let (a0, b0) := x in ⟨b0,a0 ⟩) >>> (arr_arr (fun x : c * a => let (a0, b0) := x in ⟨a0,f b0 ⟩)
    >>> (arr_first(Arrow:=ba) b g))).
  setoid_rewrite arr_exchange.
  repeat setoid_rewrite arr_associativity.
  apply arr_comp_respects; try reflexivity.
  apply arr_comp_respects; try reflexivity.
  setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; intros; simpl; try destruct X; auto; unfold extensionality; unfold bin_obj;
    intros; auto; try destruct x; try destruct p; try destruct b0; auto.

  setoid_rewrite <- arr_associativity.
  apply arr_comp_respects; try reflexivity.
  setoid_rewrite <- arr_comp_preserves.
  apply arr_arr_respects; intros; simpl; try destruct X; auto; unfold extensionality; unfold bin_obj;
    intros; auto; try destruct x; try destruct p; try destruct b0; auto.

  repeat setoid_rewrite arr_extension.
  repeat setoid_rewrite <- arr_comp_preserves.
  transitivity ((arr_arr(Arrow:=ba) (fun x:c*a => let (a0,b0):=x in ⟨a0,f b0 ⟩)) >>> (arr_first(Arrow:=ba) b g));
  [ setoid_rewrite arr_exchange | idtac ];
  apply arr_comp_respects; try reflexivity;
  apply arr_arr_respects; intros; simpl; try destruct X; auto; unfold extensionality; unfold bin_obj;
    intros; auto; try destruct x; try destruct p; try destruct b0; auto.

  intros; simpl; unfold bin_obj; reflexivity.
  intros; simpl; unfold bin_obj; reflexivity.
  intros; simpl; unfold bin_obj; reflexivity.
  intros; simpl; unfold bin_obj; reflexivity.
  intros; simpl; unfold bin_obj; reflexivity.
  Defined.

Theorem converter (fc:FreydCategory coqPreMonoidalCat) : forall q:Type, freyd_K(FreydCategory:=fc).
   intros. exact q. Defined.

Notation "` x" := (converter _ x) (at level 1)      : temporary_scope1.
Notation "`( x )" := (converter _ x)                : temporary_scope1.
Open Scope temporary_scope1.
Notation "a ~~> b" := (freyd_K_hom a b)             : category_scope.

Close Scope arrow_scope.
Open Scope arrow_scope.
Open Scope category_scope.

Lemma inverse_of_identity_is_identity : forall `{C:Category}{a:C}(i:Isomorphic a a), #i ~~ (id a) -> #i⁻¹ ~~ (id a).
  intros.
  transitivity (#i >>> #i⁻¹).
  setoid_rewrite H.
  symmetry; apply left_identity.
  apply iso_comp1.
  Qed.

Lemma iso_both_sides' :
  forall `{C:Category}{a b c d:C}(f:a~>b)(g:c~>d)(i1:Isomorphic d b)(i2:Isomorphic c a),
  f >>> #i1 ⁻¹ ~~ #i2 ⁻¹ >>> g
  -> 
  #i2 >>> f ~~ g >>> #i1.
  symmetry.
  apply iso_shift_right.
  setoid_rewrite <- associativity.
  symmetry.
  apply iso_shift_left.
  auto.
  Qed.

Lemma l1 (fc:FreydCategory coqPreMonoidalCat)`(f:a->b)(d:Type) :
  fc \ f ⋉ `d ~~ fc \ (fun xy : a * d => let (a0, b0) := xy in ⟨f a0, b0 ⟩).
  intros; set (freyd_K(FreydCategory:=fc)) as kc.
  apply (monic #(mf_preserves_first(PreMonoidalFunctor:=fc) d b)).
    apply iso_monic.
  symmetry.
  set (ni_commutes (mf_preserves_first(PreMonoidalFunctor:=fc) d) f) as help.
    simpl in help.
    symmetry in help.
    apply (transitivity(R:=eqv _ _) help).
    clear help.
  transitivity (id _ >>> fc \ f ⋉ `d).
  apply comp_respects; try reflexivity.
  set (freyd_F_strict_first d a) as help.
    simpl in help. apply help.
  symmetry.
  transitivity (fc \ f ⋉ `d  >>> id _).
  apply comp_respects; try reflexivity.
  set (freyd_F_strict_first d b) as help.
    simpl in help. apply help.
  transitivity (fc \ f ⋉ `d).
  apply right_identity.
  symmetry; apply left_identity.
  Qed.

Lemma l2 (fc : FreydCategory coqPreMonoidalCat) : forall `(f:`a~~>`b)`(g:c->d),
  fc \ (fun xy : a * c => let (a0, b0) := xy in ⟨a0, g b0 ⟩) >>> f ⋉ `d ~~
  f ⋉ `c >>> fc \ (fun xy : b * c => let (a0, b0) := xy in ⟨a0, g b0 ⟩).
  intros; set (freyd_K(FreydCategory:=fc)) as kc.
  symmetry.
  apply (monic #((mf_preserves_second(PreMonoidalFunctor:=fc) b d))).
    apply iso_monic.
  transitivity (f ⋉ `c >>> ((fc \ (fun xy : b * c => let (a0, b0) := xy in ⟨a0, g b0 ⟩)) >>>
  #(mf_preserves_second(PreMonoidalFunctor:=fc) `b d))).
    apply associativity.
  transitivity (f ⋉ `c >>> (#(mf_preserves_second(PreMonoidalFunctor:=fc) `b c) >>> (fc >>>> bin_second (fc b)) \ g)).
    apply comp_respects; try reflexivity.
    symmetry.
    apply (ni_commutes ( (mf_preserves_second(PreMonoidalFunctor:=fc) b)) g).
  symmetry.
  transitivity (((fc \ (fun xy : a * c => let (a0, b0) := xy in ⟨a0, g b0 ⟩) >>> f ⋉ `d)) >>> id _).
    apply comp_respects; try reflexivity.
    apply (freyd_F_strict_second(FreydCategory:=fc) b d).
  transitivity (((fc \ (fun xy : a * c => let (a0, b0) := xy in ⟨a0, g b0 ⟩) >>> f ⋉ `d))).
    apply right_identity.
  symmetry.
  transitivity (f ⋉ `c >>> (id (`(b*c)) >>> (fc >>>> bin_second (fc b)) \ g)).
    apply comp_respects; [ reflexivity | idtac ].
    apply comp_respects; [
      apply (freyd_F_strict_second(FreydCategory:=fc) b c) |
      reflexivity ].
  transitivity (f ⋉ `c >>> (fc >>>> bin_second (fc b)) \ g).
    apply comp_respects; [ reflexivity | apply left_identity ].
  transitivity (`a ⋊ fc \ g >>> f ⋉ `d).
    assert (CentralMorphism (fc \ g)). apply freyd_F_central.
    set (centralmor_second(f:=(fc \ g)) f) as help.
    apply help.
    apply comp_respects; [ idtac | reflexivity ].
  apply (epic #(iso_inv _ _ (mf_preserves_second(PreMonoidalFunctor:=fc) a c))).
    set (iso_epic (((mf_preserves_second a) c) ⁻¹)) as q.
    apply q.
  symmetry.
  transitivity (`a ⋊ fc \ g >>> iso_backward (mf_preserves_second(PreMonoidalFunctor:=fc) `a `d)).
  apply (ni_commutes (ni_inv (mf_preserves_second(PreMonoidalFunctor:=fc) a)) g).
  transitivity (`a ⋊ fc \ g >>> id _).
  apply comp_respects; try reflexivity.
  apply (inverse_of_identity_is_identity (mf_preserves_second(PreMonoidalFunctor:=fc) `a `d)).
  apply (freyd_F_strict_second(FreydCategory:=fc) a d).
  transitivity (`a ⋊ fc \ g).
  apply right_identity.
  symmetry.
  transitivity (id _ >>> `a ⋊ fc \ g).
  apply comp_respects; try reflexivity.
  apply (inverse_of_identity_is_identity (mf_preserves_second(PreMonoidalFunctor:=fc) `a `c)).
  apply (freyd_F_strict_second(FreydCategory:=fc) a c).
  apply left_identity.
  Qed.

Lemma l3 (fc : FreydCategory coqPreMonoidalCat) : forall `(f:`a~~>`b)(c:Type),
   f ⋉ `c >>> fc \ (fun xy : b * c => let (a0, _) := xy in a0) ~~
   fc \ (fun xy : a * c => let (a0, _) := xy in a0) >>> f.
   intros; set (freyd_K(FreydCategory:=fc)) as kc.
   transitivity (f ⋉ `c >>> (fc \ (comp(Category:=coqCategory) _ _ _
               (fun xy : b * c => let (a0, _) := xy in (a0,tt))
               (fun xy : b * unit => let (a0, _) := xy in a0)))).
   apply comp_respects; [ reflexivity | idtac ].
     simpl; apply (fmor_respects(Functor:=fc)).
     simpl. intros. destruct x; auto.
   symmetry.
   transitivity (fc \ (comp(Category:=coqCategory) _ _ _
               (fun xy : a * c => let (a0, _) := xy in (a0,tt))
               (fun xy : a * unit => let (a0, _) := xy in a0)) >>> f).
   apply comp_respects; [ idtac | reflexivity ].
     simpl; apply (fmor_respects(Functor:=fc)).
     simpl. intros. destruct x; auto.
     transitivity ((fc \ (fun xy : a * c => let (a0, _) := xy in ⟨a0, tt ⟩) >>>
       fc \ (fun xy : a * unit => let (a0, _) := xy in a0)) >>> f).
   apply comp_respects; [ idtac | reflexivity ].
   symmetry; apply (fmor_preserves_comp(Functor:=fc)).
   symmetry.
   transitivity (f ⋉ `c >>>
     (fc \ (fun xy : b * c => let (a0, _) := xy in ⟨a0, tt ⟩) >>>
       fc \ (fun xy : b * unit => let (a0, _) := xy in a0))).
   apply comp_respects; [ reflexivity | idtac ].
   symmetry; apply (fmor_preserves_comp(Functor:=fc)).
   transitivity (f ⋉ `c >>> (fc \ (fun xy : b * c => let (a0, _) := xy in ⟨a0, tt ⟩) >>> #(pmon_cancelr fc b))).
     apply comp_respects; [ reflexivity | idtac ].
     apply comp_respects; [ reflexivity | idtac ].
     apply (freyd_F_strict_cr(FreydCategory:=fc) b).
   symmetry.
   transitivity ((fc \ (fun xy : a * c => let (a0, _) := xy in ⟨a0, tt ⟩) >>> #(pmon_cancelr fc a)) >>> f).
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ reflexivity | idtac ].
     apply (freyd_F_strict_cr(FreydCategory:=fc) a).
   transitivity (((`a ⋊ fc \ (fun _ : c => tt)
     >>> iso_backward (mf_preserves_second(PreMonoidalFunctor:=fc) `a unit)) >>> #(pmon_cancelr fc a)) >>> f).
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ idtac | reflexivity ].
     symmetry.
     transitivity (iso_backward (mf_preserves_second(PreMonoidalFunctor:=fc) a c) >>>
       fc \ (fun xy : a * c => let (a0, _) := xy in ⟨a0, tt ⟩)).
     symmetry.
     apply (ni_commutes (ni_inv (mf_preserves_second(PreMonoidalFunctor:=fc) a)) (fun x:c=>tt)).
     transitivity (id _ >>> fc \ (fun xy : a * c => let (a0, _) := xy in ⟨a0, tt ⟩)).
     apply comp_respects; [ idtac | reflexivity ].
     set  (inverse_of_identity_is_identity (mf_preserves_second(PreMonoidalFunctor:=fc) `a `c)) as foo.
     simpl in foo.
     apply foo.
     apply (freyd_F_strict_second(FreydCategory:=fc) a c).
     apply left_identity.
   symmetry.
     transitivity (f ⋉ `c >>>
       ((#(mf_preserves_second(PreMonoidalFunctor:=fc) b c) >>> `b ⋊ fc \ (fun _ : c => tt)) >>>
         #(pmon_cancelr fc b))).
     apply comp_respects; [ reflexivity | idtac ].
     apply comp_respects; [ idtac | reflexivity ].
     transitivity (fc \ (fun xy : b * c => let (a0, _) := xy in ⟨a0, tt ⟩)
       >>> #(mf_preserves_second(PreMonoidalFunctor:=fc) b unit)).
     symmetry.
     transitivity (fc \ (fun xy : b * c => let (a0, _) := xy in ⟨a0, tt ⟩) >>> id _).
     apply comp_respects; [ reflexivity | idtac ].
     apply (freyd_F_strict_second(FreydCategory:=fc) b unit).
     apply right_identity.
     symmetry.
     apply (ni_commutes ( (mf_preserves_second(PreMonoidalFunctor:=fc) b)) (fun x:c=>tt)).
     transitivity (f ⋉ `c >>>
       ((id _ >>> `b ⋊ fc \ (fun _ : c => tt)) >>>
         #(pmon_cancelr fc b))).
     apply comp_respects; [ reflexivity | idtac ].
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ idtac | reflexivity ].
     apply (freyd_F_strict_second(FreydCategory:=fc) b c).
     transitivity (f ⋉ `c >>>
       ((`b ⋊ fc \ (fun _ : c => tt)) >>>
         #(pmon_cancelr fc b))).
     apply comp_respects; [ reflexivity | idtac ].
     apply comp_respects; [ idtac | reflexivity ].
     apply left_identity.
     symmetry.
     transitivity (((`a ⋊ fc \ (fun _ : c => tt) >>>
       id _) >>> 
     #(pmon_cancelr fc a)) >>> f).
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ reflexivity | idtac ].
     set  (inverse_of_identity_is_identity (mf_preserves_second(PreMonoidalFunctor:=fc) `a unit)) as foo.
     simpl in foo.
     apply foo.
     apply (freyd_F_strict_second(FreydCategory:=fc) `a unit).
     transitivity (((`a ⋊ fc \ (fun _ : c => tt)) >>>  #(pmon_cancelr fc a)) >>> f).
     apply comp_respects; [ idtac | reflexivity ].
     apply comp_respects; [ idtac | reflexivity ].
     apply right_identity.
   symmetry.
   transitivity ((f ⋉ `c >>> `b ⋊ fc \ (fun _ : c => tt)) >>> #(pmon_cancelr fc b)).
     symmetry; apply associativity.
   transitivity ((`a ⋊ fc \ (fun _ : c => tt) >>> f ⋉ `unit) >>> #(pmon_cancelr fc b)).
     apply comp_respects; [ idtac | reflexivity ].
     assert (CentralMorphism (fc \ (fun _ : c => tt))).
     apply (freyd_F_central(FreydCategory:=fc)).
     apply (centralmor_second(CentralMorphism:=H)).
   transitivity (`a ⋊ fc \ (fun _ : c => tt) >>> (f ⋉ `unit >>> #(pmon_cancelr fc b))).
     apply associativity.
   symmetry.
   transitivity (`a ⋊ fc \ (fun _ : c => tt) >>> (#(pmon_cancelr fc a) >>> f)).
     apply associativity.
     apply comp_respects; [ reflexivity | idtac ].
   set (ni_commutes (pmon_cancelr fc)) as help.
     simpl in help. apply help.
   Qed.

Lemma l4 (fc : FreydCategory coqPreMonoidalCat) : forall `(f:`a~>b)(c d:Type),
   (f ⋉ `c) ⋉ `d >>> fc \ ((fun xyz:(b*c)*d => let (ab, c) := xyz in let (a0, b0) := ab in ⟨a0, ⟨b0, c ⟩ ⟩))
   ~~ fc \ ((fun xyz:(a*c)*d => let (ab, c) := xyz in let (a0, b0) := ab in ⟨a0, ⟨b0, c ⟩ ⟩)) >>> f ⋉ _.
   intros; set (freyd_K(FreydCategory:=fc)) as kc.
   simpl in f.
   symmetry.
   transitivity (#(pmon_assoc freyd_K_monoidal _ _ _) >>> f ⋉ (c*d:(freyd_K))).
   apply comp_respects; try reflexivity.
   apply (freyd_F_strict_a(FreydCategory:=fc) `a d c).
   symmetry.
   transitivity (((f ⋉ (c: (freyd_K))) ⋉ (d:(freyd_K)) >>> #(pmon_assoc freyd_K_monoidal _ _ _))).
   apply comp_respects; try reflexivity.
   apply (freyd_F_strict_a(FreydCategory:=fc) `b `d `c).
   symmetry.
   apply (iso_both_sides' _ _ (pmon_assoc fc `b d c) (pmon_assoc fc `a d c)).
   symmetry.
   transitivity ( #(ni_iso (pmon_assoc_rr(PreMonoidalCat:=(freyd_K_monoidal(FreydCategory:=fc))) `c `d) a) >>>
   (f ⋉ (c:(freyd_K))) ⋉ (d:(freyd_K))).
   apply comp_respects; try reflexivity.
   symmetry.
   apply ((pmon_coherent_r(PreMonoidalCat:=freyd_K_monoidal(FreydCategory:=fc))) a c d).
   symmetry.
   transitivity (f ⋉ (c*d:(freyd_K)) >>>
      #(ni_iso (pmon_assoc_rr(PreMonoidalCat:=(freyd_K_monoidal(FreydCategory:=fc))) _ _ ) _)).
   apply comp_respects; try reflexivity.
   symmetry.
   apply ((pmon_coherent_r(PreMonoidalCat:=freyd_K_monoidal(FreydCategory:=fc))) b c d).
   symmetry.
   simpl.
   apply (@ni_commutes _ _ _ _ _ _ _ _ _ _ (pmon_assoc_rr(PreMonoidalCat:=(freyd_K_monoidal(FreydCategory:=fc))) c d) a `b f).
   Qed.

(* Formalized Theorem 3.17 *)
Definition Arrow_from_Freyd (fc:FreydCategory coqPreMonoidalCat)
   : Arrow (fun A B => freyd_K_hom(FreydCategory:=fc) (converter fc A) (converter fc B)).
    intros.
    set (freyd_K(FreydCategory:=fc)) as kc.
    apply (@Build_Arrow 
       (fun A B => (`A) ~~> (`B))
              (fun A B => fun f:A->B => fc \ f)
              (fun (A B C : Type) (X : `A ~~> `B) (X0 : `B ~~> `C) => X >>> X0)
              (fun (A B C : coqCategory) (X : `A ~~> `B) => X ⋉ `C)
              (fun (A B : Type) (X X0 : `A ~~> `B) => X ~~ X0));
    unfold Proper; unfold Reflexive; unfold Symmetric; unfold Transitive; unfold respectful;
    intros ; simpl.
    apply Build_Equivalence.
      unfold Reflexive; intros. apply Equivalence_Reflexive.
      unfold Symmetric; intros.  apply Equivalence_Symmetric. auto.
      unfold Transitive; intros.  transitivity y; auto.
    apply comp_respects; auto.
    apply (fmor_respects(Functor:=(bin_first(BinoidalCat:=fc) `c))); auto.
    apply (fmor_respects(Functor:=fc)); auto.
    transitivity ((id _) >>> f).
      apply comp_respects; try reflexivity.
      apply (fmor_preserves_id(Functor:=fc)).
      apply left_identity.
    transitivity (f >>> (id _)).
      apply comp_respects; try reflexivity.
      apply (fmor_preserves_id(Functor:=fc)).
      apply right_identity.
    apply associativity.
    symmetry. apply (fmor_preserves_comp(Functor:=fc) f g).
    apply (l1 fc f d).
    symmetry; apply (fmor_preserves_comp(Functor:=(bin_first `d)) f g).
    apply (l2 fc f g).
    apply (l3 fc f c).
    apply (l4 fc f c d).
  Defined.

(* one half: every Arrow is isomorphic to its implied Freyd category *)
(*

(* FIXME: isomorphism of categories must be via a premonoidal functor *)


(* FIXME: the isomorphism needs to be a premonoidal functor *)
Theorem arrow_both_defs : forall `(ba:Arrow), IsomorphicCategories (Freyd_from_Arrow ba) (ba).
  intros.
  apply Build_IsomorphicCategories with (isoc_forward:=ToFunc (functor_id _))(isoc_backward:=ToFunc (functor_id _)).
    simpl. unfold EqualFunctors. intros.
    simpl; intros; apply (@heq_morphisms_intro (ba) a b _ _); auto.
    simpl. unfold EqualFunctors. intros.
    simpl; intros; apply (@heq_morphisms_intro (ba) a b _ _); auto.
  Defined.

(* the other half: [the codomain of] every Freyd category is isomorphic to its implied Arrow *)
Theorem arrow_both_defs' : forall (fc:FreydCategory coqPreMonoidalCat), IsomorphicCategories fc ((Arrow_from_Freyd fc)).
  Lemma iforward (fc:FreydCategory coqPreMonoidalCat) : Functor fc ((Arrow_from_Freyd fc)) (fun x=> x).
    intros; apply (Build_Functor fc ((Arrow_from_Freyd fc)) _ (fun a b f => f));
      intros; auto; simpl; [ idtac | reflexivity ];
      symmetry; apply (fmor_preserves_id(Functor:=fc)).
      Defined.
  Lemma ibackward (fc:FreydCategory coqPreMonoidalCat) : Functor ((Arrow_from_Freyd fc)) fc (fun x=> x).
    intros; apply (Build_Functor ((Arrow_from_Freyd fc)) fc _ (fun a b f => f));
      intros; auto; simpl; [ idtac | reflexivity ];
        apply (fmor_preserves_id(Functor:=fc)).
        Defined.
  intros; apply (@Build_IsomorphicCategories _ _ (ToFunc (iforward fc)) (ToFunc (ibackward fc))); simpl; intros; auto.
    unfold EqualFunctors; simpl; auto.
    unfold EqualFunctors; simpl; auto.
  Defined.
*)

Close Scope arrow_scope.
Close Scope temporary_scope1.
Open Scope tree_scope.

