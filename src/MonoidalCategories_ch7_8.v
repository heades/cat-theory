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

(******************************************************************************)
(* Chapter 7.8: Monoidal Categories                                           *)
(******************************************************************************)

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
