(****************************************************************************)
(* Chapter 7.1: Subcategories                                               *)
(****************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import OppositeCategories_ch1_6_2.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.

(*
 * See the README for an explanation of why there is "WideSubcategory"
 * and "FullSubcategory" but no "Subcategory"
 *)

(* a full subcategory requires nothing more than a predicate on objects *)
Class FullSubcategory `(C:Category)(Pobj:C->Type) := { }.

(* the category construction for full subcategories is simpler: *)
Instance FullSubCategoriesAreCategories `(fsc:@FullSubcategory Ob Hom C Pobj)
  : Category (sigT Pobj) (fun dom ran => (projT1 dom)~~{C}~~>(projT1 ran)) :=
{ id   := fun t         => id (projT1 t)
; eqv  := fun a b f g   => eqv _ _ f g
; comp := fun a b c f g => f >>> g
}.
  intros; apply Build_Equivalence. unfold Reflexive.
     intros; reflexivity.
     unfold Symmetric; intros; simpl; symmetry; auto.
     unfold Transitive; intros; simpl. transitivity y; auto.
  intros; unfold Proper. unfold respectful. intros. simpl. apply comp_respects. auto. auto.
  intros; simpl. apply left_identity.
  intros; simpl. apply right_identity.
  intros; simpl. apply associativity.
  Defined.
Coercion FullSubCategoriesAreCategories : FullSubcategory >-> Category.

(* every category is a subcategory of itself! *)
(*
Instance IdentitySubCategory `(C:Category Ob Hom) : SubCategory C (fun _ => True) (fun _ _ _ _ _ => True).
  intros; apply Build_SubCategory.
  intros; auto.
  intros; auto.
  Defined.
(* the inclusion operation from a subcategory to its host is a functor *)
Instance InclusionFunctor `(C:Category Ob Hom)`(SP:@SubCategory _ _ C Pobj Pmor)
  : Functor SP C (fun x => projT1 x) :=
  { fmor := fun dom ran f => projT1 f }.
  intros. unfold eqv in H. simpl in H. auto.
  intros. simpl. reflexivity.
  intros. simpl. reflexivity.
  Defined.
*)


(* a wide subcategory includes all objects, so it requires nothing more than a predicate on each hom-set *)
Class WideSubcategory `(C:Category Ob Hom)(Pmor:forall a b:Ob, (a~>b) ->Type) : Type :=
{ wsc_id_included    : forall (a:Ob), Pmor a a (id a)
; wsc_comp_included  : forall (a b c:Ob) f g, (Pmor a b f) -> (Pmor b c g) -> (Pmor a c (f>>>g))
}.

(* the category construction for full subcategories is simpler: *)
Instance WideSubCategoriesAreCategories `{C:Category(Ob:=Ob)}{Pmor}(wsc:WideSubcategory C Pmor)
  : Category Ob (fun x y => sigT (Pmor x y)) :=
  { id   := fun t         => existT _ (id t) (@wsc_id_included _ _ _ _ wsc t)
  ; eqv  := fun a b f g   => eqv _ _ (projT1 f) (projT1 g)
  ; comp := fun a b c f g => existT (Pmor a c) (projT1 f >>> projT1 g)
                                    (@wsc_comp_included _ _ _ _ wsc _ _ _ _ _ (projT2 f) (projT2 g))

  }.
  intros; apply Build_Equivalence. unfold Reflexive.
     intros; reflexivity.
     unfold Symmetric; intros; simpl; symmetry; auto.
     unfold Transitive; intros; simpl. transitivity (projT1 y); auto.
  intros; unfold Proper. unfold respectful. intros. simpl. apply comp_respects. auto. auto.
  intros; simpl. apply left_identity.
  intros; simpl. apply right_identity.
  intros; simpl. apply associativity.
  Defined.
Coercion WideSubCategoriesAreCategories : WideSubcategory >-> Category.

(* the full image of a functor is a full subcategory *)
Section FullImage.

  Context `(F:Functor(c1:=C)(c2:=D)).

  Instance FullImage : Category C (fun x y => (F x)~~{D}~~>(F y)) :=
  { id    := fun t         => id (F t)
  ; eqv   := fun x y   f g => eqv(Category:=D)  _ _ f g
  ; comp  := fun x y z f g => comp(Category:=D) _ _ _ f g
  }.
  intros; apply Build_Equivalence. unfold Reflexive.
     intros; reflexivity.
     unfold Symmetric; intros; simpl; symmetry; auto.
     unfold Transitive; intros; simpl. transitivity y; auto.
  intros; unfold Proper. unfold respectful. intros. simpl. apply comp_respects. auto. auto.
  intros; simpl. apply left_identity.
  intros; simpl. apply right_identity.
  intros; simpl. apply associativity.
  Defined.

  Instance FullImage_InclusionFunctor : Functor FullImage D (fun x => F x) :=
    { fmor := fun x y f => f }.
    intros; auto.
    intros; simpl; reflexivity.
    intros; simpl; reflexivity.
    Defined.

  Instance RestrictToImage : Functor C FullImage (fun x => x) :=
    { fmor := fun a b f => F \ f }.
    intros; simpl; apply fmor_respects; auto.
    intros; simpl; apply fmor_preserves_id; auto.
    intros; simpl; apply fmor_preserves_comp; auto.
    Defined.

  Lemma RestrictToImage_splits : F ~~~~ (RestrictToImage >>>> FullImage_InclusionFunctor).
    unfold EqualFunctors; simpl; intros; apply heq_morphisms_intro.
    apply fmor_respects.
    auto.
    Defined.

End FullImage.

(*
Instance func_opSubcat `(c1:Category)`(c2:Category)`(SP:@SubCategory _ _ c2 Pobj Pmor)
  {fobj}(F:Functor c1⁽ºᑭ⁾ SP fobj) : Functor c1 SP⁽ºᑭ⁾ fobj :=
  { fmor                := fun a b f => fmor F f }.
  intros. apply (@fmor_respects _ _ _ _ _ _ _ F _ _ f f' H).
  intros. apply (@fmor_preserves_id _ _ _ _ _ _ _ F a).
  intros. apply (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ g _ f).
  Defined.
*)

(*
(* if a functor's range falls within a subcategory, then it is already a functor into that subcategory *)
Section FunctorWithRangeInSubCategory.
  Context `(Cat1:Category O1 Hom1).
  Context `(Cat2:Category O2 Hom2).
  Context (Pobj:Cat2 -> Type).
  Context (Pmor:forall a b:Cat2, (Pobj a) -> (Pobj b) -> (a~~{Cat2}~~>b) -> Type).
  Context (SP:SubCategory Cat2 Pobj Pmor).
  Context (Fobj:Cat1->Cat2).
  Section Forward.
    Context (F:Functor Cat1 Cat2 Fobj).
    Context (pobj:forall a, Pobj (F a)).
    Context (pmor:forall a b f, Pmor (F a) (F b) (pobj a) (pobj b) (F \ f)).
    Definition FunctorWithRangeInSubCategory_fobj (X:Cat1) : SP :=
      existT Pobj (Fobj X) (pobj X).
    Definition FunctorWithRangeInSubCategory_fmor (dom ran:Cat1)(X:dom~>ran) : (@hom _ _ SP
      (FunctorWithRangeInSubCategory_fobj dom) (FunctorWithRangeInSubCategory_fobj ran)).
      intros.
      exists (F \ X).
      apply (pmor dom ran X).
      Defined.
    Definition FunctorWithRangeInSubCategory : Functor Cat1 SP FunctorWithRangeInSubCategory_fobj.
      apply Build_Functor with (fmor:=FunctorWithRangeInSubCategory_fmor);
        intros;
        unfold FunctorWithRangeInSubCategory_fmor;
        simpl.
      setoid_rewrite H; auto.
      apply (fmor_preserves_id F).
      apply (fmor_preserves_comp F).
      Defined.
  End Forward.
  Section Opposite.
    Context (F:Functor Cat1 Cat2⁽ºᑭ⁾ Fobj).
    Context (pobj:forall a, Pobj (F a)).
    Context (pmor:forall a b f, Pmor (F b) (F a) (pobj b) (pobj a) (F \ f)).
    Definition FunctorWithRangeInSubCategoryOp_fobj (X:Cat1) : SP :=
      existT Pobj (Fobj X) (pobj X).
    Definition FunctorWithRangeInSubCategoryOp_fmor (dom ran:Cat1)(X:dom~>ran) :
      (FunctorWithRangeInSubCategoryOp_fobj dom)~~{SP⁽ºᑭ⁾}~~>(FunctorWithRangeInSubCategoryOp_fobj ran).
      intros.
      exists (F \ X).
      apply (pmor dom ran X).
      Defined.
    (*
    Definition FunctorWithRangeInSubCategoryOp : Functor Cat1 SP⁽ºᑭ⁾ FunctorWithRangeInSubCategoryOp_fobj.
      apply Build_Functor with (fmor:=FunctorWithRangeInSubCategoryOp_fmor);
        intros;
        unfold FunctorWithRangeInSubCategoryOp_fmor;
        simpl.
      apply (fmor_respects(Functor:=F)); auto.
      apply (fmor_preserves_id(Functor:=F)).
      unfold eqv; simpl.
      set (@fmor_preserves_comp _ _ _ _ _ _ _ F _ _ f _ g) as qq.
      setoid_rewrite <- qq.
      apply reflexivity.
      Defined.
      *)
  End Opposite.
End FunctorWithRangeInSubCategory.
*)


(* Definition 7.1: faithful functors *)
Definition FaithfulFunctor `(F:Functor(c1:=C1)(c2:=C2)(fobj:=Fobj)) :=
  forall (a b:C1), forall (f f':a~>b), (fmor _ f)~~(fmor _ f') -> f~~f'.

(* Definition 7.1: full functors *)
Class FullFunctor `(F:Functor(c1:=C1)(c2:=C2)(fobj:=Fobj)) :=
  { ff_invert         : forall {a b}(f:(Fobj a)~~{C2}~~>(Fobj b)) , { f' : a~~{C1}~~>b & (F \ f') ~~ f }
  ; ff_respects       : forall {a b}, Proper (eqv (Fobj a) (Fobj b) ==> eqv a b) (fun x => projT1 (@ff_invert a b x))
  }.
  Coercion ff_invert : FullFunctor >-> Funclass.

(* Definition 7.1: (essentially) surjective on objects *)
Definition EssentiallySurjectiveOnObjects `(F:Functor(c1:=C1)(c2:=C2)(fobj:=Fobj)) :=
  forall o2:C2, { o1:C1 & (F o1) ≅ o2 }.

(* Definition 7.1: (essentially) injective on objects *)
Class ConservativeFunctor `(F:Functor(c1:=C1)(c2:=C2)(fobj:=Fobj)) :=
  { cf_reflect_iso  : forall (a b:C1),  (F a) ≅ (F b) -> a ≅ b
  ; cf_reflect_iso1 : forall a b (i:(F a) ≅ (F b)), F \ #(cf_reflect_iso a b i) ~~ #i
  ; cf_reflect_iso2 : forall a b (i:(F a) ≅ (F b)), F \ #(cf_reflect_iso a b i)⁻¹ ~~ #i⁻¹
  }.

(* "monic up to natural iso" *)
Definition WeaklyMonic
    `{C:Category}
    `{D:Category}
     {Fobj}
     (F:@Functor _ _ C _ _ D Fobj) := forall
     Eob EHom (E:@Category Eob EHom)
    `{G :@Functor _ _ E _ _ C Gobj'}
    `{H :@Functor _ _ E _ _ C Hobj'},
    G >>>> F ≃ H >>>> F
    -> G ≃ H.

(*
Section FullFaithfulFunctor_section.
  Context `(F:Functor(c1:=C1)(c2:=C2)(fobj:=Fobj)).
  Context  (F_full:FullFunctor F).
  Context  (F_faithful:FaithfulFunctor F).

  Lemma ff_functor_section_id_preserved : forall a:C1, projT1 (F_full _ _ (id (F a))) ~~ id a.
    intros.
    set (F_full a a (id (F a))) as qq.
    destruct qq.
    simpl.
    apply F_faithful.
    setoid_rewrite fmor_preserves_id.
    auto.
    Qed.

  Definition ff_functor_section_fobj (a:FullImage F) : C1 := projT1 (projT2 a).

  Definition ff_functor_section_fmor {a b:FullImage F} (f:a~~{FullImage F}~~>b)
    : (ff_functor_section_fobj a)~~{C1}~~>(ff_functor_section_fobj b).
    destruct a as [ a1 [ a2 a3 ] ].
    destruct b as [ b1 [ b2 b3 ] ].
    set (@ff_invert _ _ _ _ _ _ _ _ F_full _ _ f) as f'.
    destruct a as [ a1 [ a2 a3 ] ].
    subst.
    unfold ff_functor_section_fobj.
    simpl.
    destruct b as [ b1 [ b2 b3 ] ].
    subst.
    unfold ff_functor_section_fobj.
    simpl.
    apply (@ff_invert _ _ _ _ _ _ _ _ F_full).
    apply f.
    Defined.

  Lemma ff_functor_section_respectful {a2 b2 c2 : C1}
    (x0 : Fobj b2 ~~{ C2 }~~> Fobj c2)
    (x  : Fobj a2 ~~{ C2 }~~> Fobj b2) :
    (let (x1, _) := F_full a2 b2 x in x1) >>>
    (let (x1, _) := F_full b2 c2 x0 in x1) ~~
    (let (x1, _) := F_full a2 c2 (x >>> x0) in x1).
    set (F_full _ _ x) as x_full.
    set (F_full _ _ x0) as x0_full.
    set (F_full _ _ (x >>> x0)) as x_x0_full.
    destruct x_full.
    destruct x0_full.
    destruct x_x0_full.
    apply F_faithful.
    setoid_rewrite e1.
    setoid_rewrite <- (fmor_preserves_comp F).
    setoid_rewrite e.
    setoid_rewrite e0.
    reflexivity.
    Qed.

  Instance ff_functor_section_functor : Functor (FullImage F) C1 ff_functor_section_fobj :=
    { fmor := fun a b f => ff_functor_section_fmor f }.
    abstract (intros;
      destruct a; destruct b; destruct s; destruct s0; simpl in *;
      subst; simpl; set (F_full x1 x2 f) as ff1; set (F_full x1 x2 f') as ff2; destruct ff1; destruct ff2;
      apply F_faithful;
      etransitivity; [ apply e | idtac ];
      symmetry;
      etransitivity; [ apply e0 | idtac ];
      symmetry; auto).
    abstract (intros;
      simpl;
      destruct a as [ a1 [ a2 a3 ] ];
      subst;
      simpl;
      apply ff_functor_section_id_preserved).
    abstract (intros;
      destruct a as [ a1 [ a2 a3 ] ];
      destruct b as [ b1 [ b2 b3 ] ];
      destruct c as [ c1 [ c2 c3 ] ];
      subst;
      simpl in *;
      simpl in *;
      apply ff_functor_section_respectful).
      Defined.

  Lemma ff_functor_section_splits_helper (a2 b2:C1)(f:existT (fun d : C2, {c : C1 & Fobj c = d}) (Fobj a2)
        (existT (fun c : C1, Fobj c = Fobj a2) a2 (eq_refl _)) ~~{ 
      FullImage F
      }~~> existT (fun d : C2, {c : C1 & Fobj c = d}) 
             (Fobj b2) (existT (fun c : C1, Fobj c = Fobj b2) b2 (eq_refl _)))
     : F \ (let (x1, _) := F_full a2 b2 f in x1) ~~ f.
    simpl.
    set (F_full a2 b2 f) as qq.
    destruct qq.
    apply e.
    Qed.

  Lemma ff_functor_section_splits : (ff_functor_section_functor >>>> RestrictToImage F) ~~~~ functor_id _.
    unfold EqualFunctors.
    intros.
    simpl.
    destruct a as [ a1 [ a2 a3 ] ].
    destruct b as [ b1 [ b2 b3 ] ].
    subst.
    simpl in *.
    simpl in *.
    apply heq_morphisms_intro.
    simpl.
    unfold RestrictToImage_fmor; simpl.
    etransitivity; [ idtac | apply H ].
    clear H.
    clear f'.
    apply ff_functor_section_splits_helper.
    Qed.

  Definition ff_functor_section_splits_niso_helper a : ((ff_functor_section_functor >>>> RestrictToImage F) a ≅ (functor_id (FullImage F)) a).
    intros; simpl.
    unfold functor_fobj.
    unfold ff_functor_section_fobj.
    unfold RestrictToImage_fobj.
    destruct a as [ a1 [ a2 a3 ] ].
    simpl.
    subst.
    unfold functor_fobj.
    apply iso_id.
    Defined.

  Lemma ff_functor_section_splits_niso : (ff_functor_section_functor >>>> RestrictToImage F) ≃ functor_id _.
    intros; simpl.
    exists ff_functor_section_splits_niso_helper.
    intros.
    simpl in *.
    destruct A as [ a1 [ a2 a3 ] ].
    destruct B as [ b1 [ b2 b3 ] ].
    simpl.
    unfold RestrictToImage_fmor; simpl.
    setoid_rewrite left_identity.
    setoid_rewrite right_identity.
    set (F_full a2 b2 x) as qr.
    destruct qr.
    symmetry; auto.
    Qed.

  Definition ff_functor_section_splits_niso_helper' a
    : ((RestrictToImage F >>>> ff_functor_section_functor) a ≅ (functor_id _) a).
    intros; simpl.
    unfold functor_fobj.
    unfold ff_functor_section_fobj.
    unfold RestrictToImage_fobj.
    simpl.
    apply iso_id.
    Defined.

  Lemma ff_functor_section_splits_niso' : (RestrictToImage F >>>> ff_functor_section_functor) ≃ functor_id _.
    intros; simpl.
    exists ff_functor_section_splits_niso_helper'.
    intros.
    simpl in *.
    setoid_rewrite left_identity.
    setoid_rewrite right_identity.
    set (F_full _ _ (F \ f)) as qr.
    destruct qr.
    apply F_faithful in e.
    symmetry.
    auto.
    Qed.

  Context (CF:ConservativeFunctor F).

  Lemma if_fullimage `{C0:Category}{Aobj}{Bobj}{A:Functor C0 C1 Aobj}{B:Functor C0 C1 Bobj} :
    A >>>> F ≃ B >>>> F ->
    A >>>> RestrictToImage F ≃ B >>>> RestrictToImage F.
    intro H.
    destruct H.
    unfold IsomorphicFunctors.
    set (fun A  => functors_preserve_isos (RestrictToImage F) (cf_reflect_iso _ _ (x A))).
    exists i.
    intros.
    unfold RestrictToImage.
    unfold functor_comp.
    simpl.
    unfold functor_comp in H.
    simpl in H.
    rewrite (cf_reflect_iso1(ConservativeFunctor:=CF) _ _ (x A0)).
    rewrite (cf_reflect_iso1(ConservativeFunctor:=CF) _ _ (x B0)).
    apply H.
    Qed.

  Lemma ffc_functor_weakly_monic : ConservativeFunctor F -> WeaklyMonic F.
    intro H.
    unfold WeaklyMonic; intros.
    apply (if_comp(F2:=G>>>>functor_id _)).
    apply if_inv.
    apply if_right_identity.
    apply if_inv.
    apply (if_comp(F2:=H0>>>>functor_id _)).
    apply if_inv.
    apply if_right_identity.
    eapply if_inv.
    apply (if_comp(F2:=G>>>>(RestrictToImage F >>>> ff_functor_section_functor))).
    apply (@if_respects _ _ _ _ _ _ _ _ _ _ G _ G _ (functor_id C1) _ (RestrictToImage F >>>> ff_functor_section_functor)).
    apply if_id.
    apply if_inv.
    apply ff_functor_section_splits_niso'.
    apply if_inv.
    apply (if_comp(F2:=H0>>>>(RestrictToImage F >>>> ff_functor_section_functor))).
    apply (@if_respects _ _ _ _ _ _ _ _ _ _ H0 _ H0 _ (functor_id C1) _ (RestrictToImage F >>>> ff_functor_section_functor)).
    apply if_id.
    apply if_inv.
    apply ff_functor_section_splits_niso'.
    assert
      ((H0 >>>> (RestrictToImage F >>>> ff_functor_section_functor))
        ≃ ((H0 >>>> RestrictToImage F) >>>> ff_functor_section_functor)).
    apply if_inv.
    apply if_associativity.
    apply (if_comp H2).
    clear H2.
    apply if_inv.
    assert
      ((G >>>> (RestrictToImage F >>>> ff_functor_section_functor))
        ≃ ((G >>>> RestrictToImage F) >>>> ff_functor_section_functor)).
    apply if_inv.
    apply if_associativity.
    apply (if_comp H2).
    clear H2.
    apply if_respects.
    apply if_fullimage.
    apply H1.
    apply if_id.
    Qed.

  Opaque ff_functor_section_splits_niso_helper.

End FullFaithfulFunctor_section.
*)