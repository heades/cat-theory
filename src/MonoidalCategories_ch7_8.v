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

(******************************************************************************)
(* Chapter 7.8: (Pre)Monoidal Categories                                      *)
(******************************************************************************)

Class BinoidalCat
`( C                  :  Category                               )
( bin_obj'            :  C -> C -> C                            ) :=
{ bin_obj             := bin_obj' where "a ⊗ b" := (bin_obj a b)
; bin_first           :  forall a:C, Functor C C (fun x => x⊗a)
; bin_second          :  forall a:C, Functor C C (fun x => a⊗x)
; bin_c               := C
}.
Coercion bin_c : BinoidalCat >-> Category.
Notation "a ⊗ b"  := (@bin_obj _ _ _ _ _ a b)                              : category_scope.
Notation "C ⋊ f"  := (@fmor _ _ _ _ _ _ _ (@bin_second _ _ _ _ _ C) _ _ f) : category_scope.
Notation "g ⋉ C"  := (@fmor _ _ _ _ _ _ _ (@bin_first _ _ _ _ _ C) _ _ g)  : category_scope.
Notation "C ⋊ -"  := (@bin_second _ _ _ _ _ C)                             : category_scope.
Notation "- ⋉ C"  := (@bin_first _ _ _ _ _ C)                              : category_scope.

Class CentralMorphism `{BinoidalCat}`(f:a~>b) : Prop := 
{ centralmor_first  : forall `(g:c~>d), (f ⋉ _ >>> _ ⋊ g) ~~ (_ ⋊ g >>> f ⋉ _)
; centralmor_second : forall `(g:c~>d), (g ⋉ _ >>> _ ⋊ f) ~~ (_ ⋊ f >>> g ⋉ _)
}.

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

Class CommutativeCat `(BinoidalCat) :=
{ commutative_central  :  forall `(f:a~>b), CentralMorphism f
; commutative_morprod  := fun `(f:a~>b)`(g:a~>b) => f ⋉ _ >>> _ ⋊ g
}.
Notation "f × g"    := (commutative_morprod f g).

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

End BinoidalCat_from_Bifunctor.

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

(* Definition 7.23 *)
Class MonoidalCat `{C:Category}{Fobj:prod_obj C C -> C}{F:Functor (C ×× C) C Fobj}(I:C) :=
{ mon_f         := F
; mon_i         := I
; mon_c         := C
; mon_first     := fun a b c (f:a~>b) => F \ pair_mor (pair_obj a c) (pair_obj b c) f (id c)
; mon_second    := fun a b c (f:a~>b) => F \ pair_mor (pair_obj c a) (pair_obj c b) (id c) f
; mon_cancelr   :  (func_rlecnac I >>>> F) <~~~> functor_id C
; mon_cancell   :  (func_llecnac I >>>> F) <~~~> functor_id C
; mon_assoc     :  ((F **** (functor_id C)) >>>> F) <~~~> func_cossa >>>> ((((functor_id C) **** F) >>>> F))
; mon_pentagon  :  Pentagon mon_first mon_second (fun a b c => #(mon_assoc (pair_obj (pair_obj a b) c)))
; mon_triangle  :  Triangle mon_first mon_second (fun a b c => #(mon_assoc (pair_obj (pair_obj a b) c)))
                                                 (fun a => #(mon_cancell a)) (fun a => #(mon_cancelr a))
}.
(* Coq manual on coercions: ... only the oldest one is valid and the
 * others are ignored. So the order of declaration of coercions is
 * important. *)
Coercion mon_c   : MonoidalCat >-> Category.
Coercion mon_f   : MonoidalCat >-> Functor.
Implicit Arguments mon_f [Ob Hom C Fobj F I].
Implicit Arguments mon_i [Ob Hom C Fobj F I].
Implicit Arguments mon_c [Ob Hom C Fobj F I].
Implicit Arguments MonoidalCat [Ob Hom ].

Section MonoidalCat_is_PreMonoidal.
  Context `(M:MonoidalCat).
  Definition mon_bin_M := BinoidalCat_from_Bifunctor (mon_f M).
  Existing Instance mon_bin_M.
  Lemma mon_pmon_assoc : forall a b, (bin_second a >>>> bin_first b) <~~~> (bin_first b >>>> bin_second a).
    intros.
    set (fun c => mon_assoc (pair_obj (pair_obj a c) b)) as qq.
    simpl in qq.
    apply Build_NaturalIsomorphism with (ni_iso:=qq).
    abstract (intros; set ((ni_commutes mon_assoc) (pair_obj (pair_obj a A) b) (pair_obj (pair_obj a B) b)
                    (pair_mor (pair_obj (pair_obj a A) b) (pair_obj (pair_obj a B) b)
                    (pair_mor (pair_obj a A) (pair_obj a B) (id a) f) (id b))) as qr;
             apply qr).
    Defined.

  Lemma mon_pmon_assoc_rr   :  forall a b, (bin_first  (a⊗b)) <~~~> (bin_first  a >>>> bin_first  b).
    intros.
    set (fun c:C => mon_assoc (pair_obj (pair_obj c a) b)) as qq.
    simpl in qq.
    apply ni_inv.
    apply Build_NaturalIsomorphism with (ni_iso:=qq).
    abstract (intros; set ((ni_commutes mon_assoc) (pair_obj (pair_obj _ _) _) (pair_obj (pair_obj _ _) _)
                    (pair_mor (pair_obj (pair_obj _ _) _) (pair_obj (pair_obj _ _) _)
                    (pair_mor (pair_obj _ _) (pair_obj _ _) f (id a)) (id b))) as qr;
              etransitivity; [ idtac | apply qr ];
              apply comp_respects; try reflexivity;
              unfold mon_f;
              simpl;
              apply ((fmor_respects F) (pair_obj _ _) (pair_obj _ _));
              split; try reflexivity;
              symmetry;
              simpl;
              set (@fmor_preserves_id _ _ _ _ _ _ _ F (pair_obj a b)) as qqqq;
              simpl in qqqq;
              apply qqqq).
   Defined.

  Lemma mon_pmon_assoc_ll   :  forall a b, (bin_second (a⊗b)) <~~~> (bin_second b >>>> bin_second a).
    intros.
    set (fun c:C => mon_assoc (pair_obj (pair_obj a b) c)) as qq.
    simpl in qq.
    set (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ (Fobj (pair_obj a b) ⋊-) (b ⋊- >>>> a ⋊-)) as qqq.
    set (qqq qq) as q'.
    apply q'.
    clear q'.
    clear qqq.
    abstract (intros; set ((ni_commutes mon_assoc) (pair_obj (pair_obj _ _) _) (pair_obj (pair_obj _ _) _)
                    (pair_mor (pair_obj (pair_obj _ _) _) (pair_obj (pair_obj _ _) _)
                    (pair_mor (pair_obj _ _) (pair_obj _ _) (id a) (id b)) f)) as qr;
              etransitivity; [ apply qr | idtac ];
              apply comp_respects; try reflexivity;
              unfold mon_f;
              simpl;
              apply ((fmor_respects F) (pair_obj _ _) (pair_obj _ _));
              split; try reflexivity;
              simpl;
              set (@fmor_preserves_id _ _ _ _ _ _ _ F (pair_obj a b)) as qqqq;
              simpl in qqqq;
              apply qqqq).
    Defined.

  Lemma mon_pmon_cancelr : (bin_first I0) <~~~> functor_id C.
    set (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ (bin_first I0) (functor_id C)) as qq.
    set (mon_cancelr) as z.
    simpl in z.
    simpl in qq.
    set (qq z) as zz.
    apply zz.
    abstract (intros;
              set (ni_commutes mon_cancelr) as q; simpl in *;
              apply q).
    Defined.

  Lemma mon_pmon_cancell : (bin_second I0) <~~~> functor_id C.
    set (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ (bin_second I0) (functor_id C)) as qq.
    set (mon_cancell) as z.
    simpl in z.
    simpl in qq.
    set (qq z) as zz.
    apply zz.
    abstract (intros;
              set (ni_commutes mon_cancell) as q; simpl in *;
              apply q).
    Defined.

  Lemma mon_pmon_triangle : forall a b, #(mon_pmon_cancelr a) ⋉ b ~~ #(mon_pmon_assoc _ _ _) >>> a ⋊ #(mon_pmon_cancell b).
    intros.
    set mon_triangle as q.
    simpl in q.
    apply q.
    Qed.

  Lemma mon_pmon_pentagon a b c d : (#(mon_pmon_assoc a c b ) ⋉ d)  >>>
                                     #(mon_pmon_assoc a d _ )   >>>
                                (a ⋊ #(mon_pmon_assoc b d c))
                                  ~~ #(mon_pmon_assoc _ d c )   >>>
                                     #(mon_pmon_assoc a _ b ).
    set (@pentagon _ _ _ _ _ _ _ mon_pentagon) as x.
    simpl in x.
    unfold bin_obj.
    unfold mon_first in x.
    simpl in *.
    apply x.
    Qed.

  Definition MonoidalCat_is_PreMonoidal : PreMonoidalCat (BinoidalCat_from_Bifunctor (mon_f M)) (mon_i M).
    refine {| pmon_assoc                 := mon_pmon_assoc
            ; pmon_cancell               := mon_pmon_cancell
            ; pmon_cancelr               := mon_pmon_cancelr
            ; pmon_triangle              := {| triangle := mon_pmon_triangle |}
            ; pmon_pentagon              := {| pentagon := mon_pmon_pentagon |}
            ; pmon_assoc_ll              := mon_pmon_assoc_ll
            ; pmon_assoc_rr              := mon_pmon_assoc_rr
            |}.
    abstract (set (coincide mon_triangle) as qq; simpl in *; apply qq).
    abstract (intros; simpl; reflexivity).
    abstract (intros; simpl; reflexivity).
    Defined.

  Lemma MonoidalCat_all_central : forall a b (f:a~~{M}~~>b), CentralMorphism f.
    intros;
    set (@fmor_preserves_comp _ _ _ _ _ _ _ M) as fc.
    apply Build_CentralMorphism;
    intros; simpl in *.
    etransitivity.
      apply fc.
      symmetry.
      etransitivity.
      apply fc.
      apply (fmor_respects M).
      simpl.
      setoid_rewrite left_identity;
      setoid_rewrite right_identity;
      split; reflexivity.
    etransitivity.
      apply fc.
      symmetry.
      etransitivity.
      apply fc.
      apply (fmor_respects M).
      simpl.
      setoid_rewrite left_identity;
      setoid_rewrite right_identity;
      split; reflexivity.
    Qed.

End MonoidalCat_is_PreMonoidal.

Hint Extern 1 => apply MonoidalCat_all_central.
Coercion MonoidalCat_is_PreMonoidal : MonoidalCat >-> PreMonoidalCat.

(* Later: generalize to premonoidal categories *)
Class DiagonalCat `(mc:MonoidalCat(F:=F)) :=
{  copy_nt      :  forall a, functor_id _ ~~~> func_diagonal >>>> F
;  copy         :  forall (a:mc),   a~~{mc}~~>(bin_obj(BinoidalCat:=mc) a a)
                := fun a => nt_component _ _ (copy_nt a) a
(* for non-cartesian braided diagonal categories we also need: copy >> swap == copy *)
}.

(* TO DO: show that the endofunctors on any given category form a monoidal category *)
Section MonoidalFunctor.
  Context `(m1:MonoidalCat(C:=C1)) `(m2:MonoidalCat(C:=C2)).
  Class MonoidalFunctor {Mobj:C1->C2} (mf_F:Functor C1 C2 Mobj) :=
  { mf_f         := mf_F where "f ⊕⊕ g" := (@fmor _ _ _ _ _ _ _ m2 _ _ (pair_mor (pair_obj _ _) (pair_obj _ _) f g))
  ; mf_coherence :  (mf_F **** mf_F) >>>> (mon_f m2) <~~~> (mon_f m1) >>>> mf_F
  ; mf_phi       := fun a b => #(mf_coherence (pair_obj a b))
  ; mf_id        :  (mon_i m2) ≅ (mf_F (mon_i m1))
  ; mf_cancelr   :  forall a,    #(mon_cancelr(MonoidalCat:=m2) (mf_F a)) ~~
                                  (id (mf_F a)) ⊕⊕ #mf_id >>> mf_phi a (mon_i _) >>> mf_F \ #(mon_cancelr a)
  ; mf_cancell   :  forall b,    #(mon_cancell (mf_F b)) ~~
                                 #mf_id ⊕⊕ (id (mf_F b)) >>> mf_phi (mon_i _) b >>> mf_F \ #(mon_cancell b)
  ; mf_assoc     :  forall a b c, (mf_phi a b) ⊕⊕ (id (mf_F c)) >>> (mf_phi _ c) >>>
                                  (mf_F \ #(mon_assoc (pair_obj (pair_obj a b) c) )) ~~
                                          #(mon_assoc (pair_obj (pair_obj _ _) _) )  >>>
                                  (id (mf_F a)) ⊕⊕ (mf_phi b c) >>> (mf_phi a _)
  }.
End MonoidalFunctor.
Coercion mf_f : MonoidalFunctor >-> Functor.
Implicit Arguments mf_coherence [ Ob Hom C1 Fobj F I0 m1 Ob0 Hom0 C2 Fobj0 F0 I1 m2 Mobj mf_F ].
Implicit Arguments mf_id        [ Ob Hom C1 Fobj F I0 m1 Ob0 Hom0 C2 Fobj0 F0 I1 m2 Mobj mf_F ].

Section MonoidalFunctorsCompose.
  Context `(m1:MonoidalCat).
  Context `(m2:MonoidalCat).
  Context `(m3:MonoidalCat).
  Context  {f1obj}(f1:@Functor _ _ m1 _ _ m2 f1obj).
  Context  {f2obj}(f2:@Functor _ _ m2 _ _ m3 f2obj).
  Context  (mf1:MonoidalFunctor m1 m2 f1).
  Context  (mf2:MonoidalFunctor m2 m3 f2).

  Lemma mf_compose_coherence : (f1 >>>> f2) **** (f1 >>>> f2) >>>> m3 <~~~> m1 >>>> (f1 >>>> f2).
    set (mf_coherence mf1) as mc1.
    set (mf_coherence mf2) as mc2.
    set (@ni_comp) as q.
    set (q _ _ _ _ _ _ _ ((f1 >>>> f2) **** (f1 >>>> f2) >>>> m3) _ ((f1 **** f1 >>>> m2) >>>> f2) _ (m1 >>>> (f1 >>>> f2))) as qq.
    apply qq; clear qq; clear q.
    apply (@ni_comp _ _ _ _ _ _ _ _ _ (f1 **** f1 >>>> (f2 **** f2 >>>> m3)) _ _).
    apply (@ni_comp _ _ _ _ _ _ _ _ _ ((f1 **** f1 >>>> f2 **** f2) >>>> m3) _ _).
    eapply ni_respects.
      apply ni_prod_comp.
      apply ni_id.
    apply ni_associativity.
    apply ni_inv.
    eapply ni_comp.
      apply (ni_associativity (f1 **** f1) m2 f2).
      apply (ni_respects (F0:=f1 **** f1)(F1:=f1 **** f1)(G0:=(m2 >>>> f2))(G1:=(f2 **** f2 >>>> m3))).
        apply ni_id.
        apply ni_inv.
        apply mc2.
    apply ni_inv.
    eapply ni_comp.
      eapply ni_inv.
      apply (ni_associativity m1 f1 f2).
      apply ni_respects.
        apply ni_inv.
        apply mc1.
        apply ni_id.
  Defined.

  Instance MonoidalFunctorsCompose : MonoidalFunctor m1 m3 (f1 >>>> f2) :=
  { mf_id        := id_comp         (mf_id mf2) (functors_preserve_isos f2 (mf_id mf1))
  ; mf_coherence := mf_compose_coherence
  }.
  admit.
  admit.
  admit.
  Defined.

End MonoidalFunctorsCompose.

Class CartesianCat `(mc:MonoidalCat) :=
{ car_terminal  : Terminal mc
; car_one       : (@one _ _ _ car_terminal) ≅ (mon_i mc)
; car_diagonal  : DiagonalCat mc
; car_law1      : forall {a}, id a ~~ (copy(DiagonalCat:=car_diagonal) a) >>> ((drop a >>> #car_one) ⋉ a) >>> (#(pmon_cancell mc _))
; car_law2      : forall {a}, id a ~~ (copy(DiagonalCat:=car_diagonal) a) >>> (a ⋊ (drop a >>> #car_one)) >>> (#(pmon_cancelr mc _))
; car_mn        := mc
}.
Coercion car_diagonal : CartesianCat >-> DiagonalCat.
Coercion car_terminal : CartesianCat >-> Terminal.
Coercion car_mn       : CartesianCat >-> MonoidalCat.

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
    admit.
    admit.
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

  Definition CenterMonoidal  : MonoidalCat _ _ CenterMonoidal_F (exist _ pI I).
    admit.
    Defined.

End CenterMonoidal.

