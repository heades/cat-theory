Generalizable All Variables.
Require Import Preamble.
Require Import General.
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
Require Import MonoidalCategories_ch7_8.

(******************************************************************************)
(* Chapter 2.8: Hom Sets and Enriched Categories                              *)
(******************************************************************************)

Class ECategory `(mn:PreMonoidalCat(bc:=bc)(C:=V)(I:=EI))(Eob:Type)(Ehom:Eob->Eob->V) :=
{ ehom               :=  Ehom where "a ~~> b" := (ehom a b)
; eob_eob            :=  Eob
; e_v                :=  mn
; eid                :   forall a,          EI~>(a~~>a)
; eid_central        :   forall a,          CentralMorphism (eid a)
; ecomp              :   forall {a b c},    (a~~>b)⊗(b~~>c) ~> (a~~>c)
; ecomp_central      :>  forall {a b c},    CentralMorphism (@ecomp a b c)
; eleft_identity     :   forall {a b  },    eid a ⋉ (a~~>b) >>> ecomp ~~ #(pmon_cancell _)
; eright_identity    :   forall {a b  },    (a~~>b) ⋊ eid b >>> ecomp ~~ #(pmon_cancelr _)
; eassociativity     :   forall {a b c d},  #(pmon_assoc _ _ (_~~>_))⁻¹ >>> ecomp ⋉ (c~~>d) >>> ecomp ~~ (a~~>b) ⋊ ecomp >>> ecomp
}.
Notation "a ~~> b" := (@ehom _ _ _ _ _ _ _ _ _ _ a b) : category_scope.
Coercion eob_eob : ECategory >-> Sortclass.

Lemma ecomp_is_functorial `{ec:ECategory}{a b c}{x}(f:EI~~{V}~~>(a~~>b))(g:EI~~{V}~~>(b~~>c)) :
   ((x ~~> a) ⋊-) \ (iso_backward (pmon_cancelr EI) >>> ((- ⋉EI) \ f >>> (((a ~~> b) ⋊-) \ g >>> ecomp))) >>> ecomp ~~
   ((x ~~> a) ⋊-) \ f >>> (ecomp >>> (#(pmon_cancelr (x ~~> b)) ⁻¹ >>> (((x ~~> b) ⋊-) \ g >>> ecomp))).

   set (@fmor_preserves_comp) as fmor_preserves_comp'.

   (* knock off the leading (x ~~> a) ⋊ f *)
   repeat setoid_rewrite <- associativity.
   set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) f) as qq.
   apply iso_shift_right' in qq.
   setoid_rewrite <- associativity in qq.
   apply symmetry in qq.
   apply iso_shift_left' in qq.
   apply symmetry in qq.
   simpl in qq.
   setoid_rewrite <- qq.
   clear qq.
   repeat setoid_rewrite associativity.
   repeat setoid_rewrite <- fmor_preserves_comp'.
   repeat setoid_rewrite associativity.
   apply comp_respects; try reflexivity.

   (* rewrite using the lemma *)
   assert (forall {a b c x}(g:EI~~{V}~~>(b ~~> c)),
    ((bin_second(BinoidalCat:=bc) (x ~~> a)) \ ((bin_second(BinoidalCat:=bc) (a ~~> b)) \ g))
    ~~
    (#(pmon_assoc (x ~~> a) _ _)⁻¹ >>>
     (bin_second(BinoidalCat:=bc) ((x ~~> a) ⊗ (a ~~> b))) \ g >>> #(pmon_assoc (x ~~> a) _ _))).
    symmetry.

    setoid_rewrite associativity.
    symmetry.
    apply iso_shift_right'.
    setoid_rewrite <- pmon_coherent_l.
    set (ni_commutes (pmon_assoc_ll (x0~~>a0) (a0~~>b0))) as qq.
    simpl in *.
    apply (qq _ _ g0).
   setoid_rewrite H.
   clear H.

   (* rewrite using eassociativity *)
   repeat setoid_rewrite associativity.
   set (@eassociativity _ _ _ _ _ _ _ _ _ ec x a) as qq.
   setoid_rewrite <- qq.
   clear qq.
   unfold e_v.

   (* knock off the trailing ecomp *)
   repeat setoid_rewrite <- associativity.
   apply comp_respects; try reflexivity.

   (* cancel out the adjacent assoc/cossa pair *)
   repeat setoid_rewrite associativity.
   setoid_rewrite juggle2.
   etransitivity.
   apply comp_respects; [ idtac | 
   repeat setoid_rewrite <- associativity;
   etransitivity; [ idtac | apply left_identity ];
   apply comp_respects; [ idtac | reflexivity ];
   apply iso_comp1 ].
   apply reflexivity.

   (* now swap the order of ecomp⋉(b ~~> c) and ((x ~~> a) ⊗ (a ~~> b))⋊g *)
   repeat setoid_rewrite associativity.
   set (@centralmor_first) as se.
   setoid_rewrite <- se.
   clear se.

   (* and knock the trailing (x ~~> b)⋊ g off *)
   repeat setoid_rewrite <- associativity.
   apply comp_respects; try reflexivity.

   (* push the ecomp forward past the rlecnac *)
   set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) (@ecomp _ _ _ _ _ _ _ _ _ ec x a b)) as qq.
   symmetry in qq.
   apply iso_shift_left' in qq.
   setoid_rewrite associativity in qq.
   symmetry in qq.
   apply iso_shift_right' in qq.
   simpl in qq.
   setoid_rewrite qq.
   clear qq.

   (* and knock off the trailing ecomp *)
   apply comp_respects; try reflexivity.

   setoid_replace (iso_backward ((pmon_cancelr) ((x ~~> a) ⊗ (a ~~> b)))) with
     (iso_backward ((pmon_cancelr) ((x ~~> a) ⊗ (a ~~> b))) >>> id _).
   simpl.
   set (@iso_shift_right') as ibs.
   simpl in ibs.
   apply ibs.
   clear ibs.

   setoid_rewrite (MacLane_ex_VII_1_1 (x~~>a) (a~~>b)).
   setoid_rewrite juggle3.
   set (fmor_preserves_comp ((x ~~> a) ⋊-)) as q.
   simpl in q.
   setoid_rewrite q.
   clear q.
   setoid_rewrite iso_comp1.
   setoid_rewrite fmor_preserves_id.
   setoid_rewrite right_identity.
   apply iso_comp1.

   (* leftovers *)
   symmetry.
   apply right_identity.
   apply ecomp_central.
   Qed.

Lemma underlying_associativity `{ec:ECategory(mn:=mn)(EI:=EI)(Eob:=Eob)(Ehom:=Ehom)} :
   forall {a b : Eob} (f : EI ~~{ V }~~> a ~~> b) {c : Eob}
   (g : EI ~~{ V }~~> b ~~> c) {d : Eob} (h : EI ~~{ V }~~> c ~~> d),
   ((((#(pmon_cancelr EI) ⁻¹ >>> (f ⋉ EI >>> (a ~~> b) ⋊ g)) >>> ecomp) ⋉ EI >>> (a ~~> c) ⋊ h)) >>> ecomp ~~
   ((f ⋉ EI >>> (a ~~> b) ⋊ ((#(pmon_cancelr EI) ⁻¹ >>> (g ⋉ EI >>> (b ~~> c) ⋊ h)) >>> ecomp))) >>> ecomp.

  intros; symmetry; etransitivity;
     [ setoid_rewrite associativity; apply comp_respects;
        [ apply reflexivity | repeat setoid_rewrite associativity; apply (ecomp_is_functorial(x:=a) g h) ] | idtac ].

  repeat setoid_rewrite <- fmor_preserves_comp.
    repeat setoid_rewrite <- associativity.
    apply comp_respects; try reflexivity.
    apply comp_respects; try reflexivity.

  set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) f) as qq.
    apply iso_shift_right' in qq.
    symmetry in qq.
    setoid_rewrite <- associativity in qq.
    apply iso_shift_left' in qq.
    apply (fmor_respects (bin_first EI)) in qq.
    setoid_rewrite <- fmor_preserves_comp in qq.
    setoid_rewrite qq.
    clear qq.

  repeat setoid_rewrite <- fmor_preserves_comp.
    repeat setoid_rewrite associativity.
    apply comp_respects; try reflexivity.

  repeat setoid_rewrite associativity.
  set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) (@ecomp _ _ _ _ _ _ _ _ _ ec a b c)) as qq.
    apply iso_shift_right' in qq.
    symmetry in qq.
    setoid_rewrite <- associativity in qq.
    apply iso_shift_left' in qq.
    symmetry in qq.
    simpl in qq.
    setoid_rewrite qq.
    clear qq.

  repeat setoid_rewrite <- associativity.
    apply comp_respects; try reflexivity.

  idtac.
    set (iso_shift_left'
         (iso_backward (pmon_cancelr (a ~~> b)) ⋉ EI >>> ((a ~~> b) ⋊ g) ⋉ EI) ((a ~~> b) ⋊ g)
         ((pmon_cancelr ((a ~~> b) ⊗ (b ~~> c))))) as xx.
    symmetry.
    etransitivity; [ apply xx | apply comp_respects; try reflexivity ].
    clear xx.

  setoid_rewrite (fmor_preserves_comp (bin_first EI)).
    set (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn) ((iso_backward (pmon_cancelr (a ~~> b)) >>> (a ~~> b) ⋊ g))) as qq.
    simpl in qq.
    setoid_rewrite <- qq.
    clear qq.

  setoid_rewrite <- associativity.
    setoid_rewrite iso_comp1.
    apply left_identity.

  Qed.

Instance Underlying `(ec:ECategory(mn:=mn)(EI:=EI)(Eob:=Eob)(Ehom:=Ehom)) : Category Eob (fun a b => EI~>(a~~>b)) :=
{ id    := fun a                                  => eid a
; comp  := fun a b c g f                          => #(pmon_cancelr _)⁻¹ >>> (g ⋉ _ >>> _ ⋊ f) >>> ecomp
; eqv   := fun a b (f:EI~>(a~~>b))(g:EI~>(a~~>b)) => f ~~ g
}.
  abstract (intros; apply Build_Equivalence;
    [ unfold Reflexive
    | unfold Symmetric
    | unfold Transitive]; intros; simpl; auto).
  abstract (intros; unfold Proper; unfold respectful; intros; simpl;
  repeat apply comp_respects; try apply reflexivity;
    [ apply (fmor_respects (bin_first EI)) | idtac ]; auto;
    apply (fmor_respects (bin_second (a~~>b))); auto).
  abstract (intros;
    set (fun c d => centralmor_first(c:=c)(d:=d)(CentralMorphism:=(eid_central a))) as q;
    setoid_rewrite q;
    repeat setoid_rewrite associativity;
    setoid_rewrite eleft_identity;
    setoid_rewrite <- (ni_commutes (@pmon_cancell _ _ _ _ _ _ mn));
    setoid_rewrite <- associativity;
    set (coincide pmon_triangle) as qq;
    setoid_rewrite qq;
    simpl;
    setoid_rewrite iso_comp2;
    apply left_identity).
  abstract (intros;
    repeat setoid_rewrite associativity;
    setoid_rewrite eright_identity;
    setoid_rewrite <- (ni_commutes (@pmon_cancelr _ _ _ _ _ _ mn));
    setoid_rewrite <- associativity;
    simpl;
    setoid_rewrite iso_comp2;
    apply left_identity).
  abstract (intros;
    repeat setoid_rewrite associativity;
    apply comp_respects; try reflexivity;
    repeat setoid_rewrite <- associativity;
    apply underlying_associativity).
  Defined.
Coercion Underlying : ECategory >-> Category.

Class EFunctor
  `{mn:PreMonoidalCat(bc:=bc)(C:=V)(I:=EI)}
   {Eob1}{EHom1}(ec1:ECategory mn Eob1 EHom1)
   {Eob2}{EHom2}(ec2:ECategory mn Eob2 EHom2)
   (EFobj : Eob1 -> Eob2)
:=
{ efunc_fobj           := EFobj
; efunc                :  forall a b:Eob1, (a ~~> b) ~~{V}~~> ( (EFobj a) ~~> (EFobj b) )
; efunc_central        :  forall a b,      CentralMorphism (efunc a b)
; efunc_preserves_id   :  forall a,        eid a >>> efunc a a ~~ eid (EFobj a)
; efunc_preserves_comp :  forall a b c,    (efunc a b) ⋉ _ >>>  _ ⋊ (efunc b c) >>> ecomp ~~ ecomp >>> efunc a c
}.
Coercion efunc_fobj : EFunctor >-> Funclass.
Implicit Arguments efunc [ Ob Hom V bin_obj' bc EI mn Eob1 EHom1 ec1 Eob2 EHom2 ec2 EFobj ].

Definition efunctor_id 
  `{mn:PreMonoidalCat(bc:=bc)(C:=V)(I:=EI)}
   {Eob1}{EHom1}(ec1:ECategory mn Eob1 EHom1)
   : EFunctor ec1 ec1 (fun x => x).
  refine {| efunc := fun a b => id (a ~~> b) |}.
  abstract (intros; apply Build_CentralMorphism; intros;
    setoid_rewrite fmor_preserves_id;
    setoid_rewrite right_identity;
    setoid_rewrite left_identity;
    reflexivity).
  abstract (intros; apply right_identity).
  abstract (intros;
    setoid_rewrite fmor_preserves_id;
    setoid_rewrite right_identity;
    setoid_rewrite left_identity;
    reflexivity).
  Defined.

Definition efunctor_comp
  `{mn:PreMonoidalCat(bc:=bc)(C:=V)(I:=EI)}
   {Eob1}{EHom1}(ec1:ECategory mn Eob1 EHom1)
   {Eob2}{EHom2}(ec2:ECategory mn Eob2 EHom2)
   {Eob3}{EHom3}(ec3:ECategory mn Eob3 EHom3)
   {Fobj}(F:EFunctor ec1 ec2 Fobj)
   {Gobj}(G:EFunctor ec2 ec3 Gobj)
   : EFunctor ec1 ec3 (Gobj ○ Fobj).
  refine {| efunc := fun a b => (efunc F a b) >>> (efunc G _ _) |}; intros; simpl.
  abstract (apply Build_CentralMorphism; intros;
    [ set (fun a b c d => centralmor_first(CentralMorphism:=(efunc_central(EFunctor:=F)) a b)(c:=c)(d:=d)) as fc1
    ; set (fun a b c d => centralmor_first(CentralMorphism:=(efunc_central(EFunctor:=G)) a b)(c:=c)(d:=d)) as gc1
    ; setoid_rewrite <- (fmor_preserves_comp (-⋉d))
    ; setoid_rewrite <- (fmor_preserves_comp (-⋉c))
    ; setoid_rewrite <- associativity
    ; setoid_rewrite <- fc1
    ; setoid_rewrite    associativity
    ; setoid_rewrite <- gc1
    ; reflexivity
    | set (fun a b c d => centralmor_second(CentralMorphism:=(efunc_central(EFunctor:=F)) a b)(c:=c)(d:=d)) as fc2
    ; set (fun a b c d => centralmor_second(CentralMorphism:=(efunc_central(EFunctor:=G)) a b)(c:=c)(d:=d)) as gc2
    ; setoid_rewrite <- (fmor_preserves_comp (d⋊-))
    ; setoid_rewrite <- (fmor_preserves_comp (c⋊-))
    ; setoid_rewrite <- associativity
    ; setoid_rewrite    fc2
    ; setoid_rewrite    associativity
    ; setoid_rewrite    gc2
    ; reflexivity ]).
  abstract (setoid_rewrite <- associativity;
    setoid_rewrite efunc_preserves_id;
    setoid_rewrite efunc_preserves_id;
    reflexivity).
  abstract (repeat setoid_rewrite associativity;
    set (fmor_preserves_comp (-⋉(b~~>c))) as q; setoid_rewrite <- q; clear q;
    repeat setoid_rewrite associativity;
    set (fmor_preserves_comp (((Gobj (Fobj a) ~~> Gobj (Fobj b))⋊-))) as q; setoid_rewrite <- q; clear q;
    set (fun d e => centralmor_second(c:=d)(d:=e)(CentralMorphism:=(efunc_central(EFunctor:=F) b c))) as qq;
    setoid_rewrite juggle2;
    setoid_rewrite juggle2;
    setoid_rewrite qq;
    clear qq;
    repeat setoid_rewrite associativity;
    set ((efunc_preserves_comp(EFunctor:=G)) (Fobj a) (Fobj b) (Fobj c)) as q;
    repeat setoid_rewrite associativity;
    repeat setoid_rewrite associativity in q;
    setoid_rewrite q;
    clear q;
    repeat setoid_rewrite <- associativity;
    apply comp_respects; try reflexivity;
    set ((efunc_preserves_comp(EFunctor:=F)) a b c) as q;
    apply q).
  Defined.

Instance UnderlyingFunctor `(EF:@EFunctor Ob Hom V bin_obj' bc EI mn Eob1 EHom1 ec1 Eob2 EHom2 ec2 Eobj)
  : Functor (Underlying ec1) (Underlying ec2) Eobj :=
  { fmor := fun a b (f:EI~~{V}~~>(a~~>b)) => f >>> (efunc _ a b) }.
  abstract (intros; simpl; apply comp_respects; try reflexivity; auto).
  abstract (intros; simpl; apply efunc_preserves_id).
  abstract (intros;
            simpl;
            repeat setoid_rewrite associativity;
            setoid_rewrite <- efunc_preserves_comp;
            repeat setoid_rewrite associativity;
              apply comp_respects; try reflexivity;
            set (@fmor_preserves_comp _ _ _ _ _ _ _ (bin_first EI)) as qq;
              setoid_rewrite <- qq;
              clear qq;
            repeat setoid_rewrite associativity;
              apply comp_respects; try reflexivity;
            repeat setoid_rewrite <- associativity;
              apply comp_respects; try reflexivity;
            set (@fmor_preserves_comp _ _ _ _ _ _ _ (bin_second (Eobj a ~~> Eobj b))) as qq;
              setoid_rewrite <- qq;
              repeat setoid_rewrite <- associativity;
              apply comp_respects; try reflexivity;
              clear qq;
            apply (centralmor_first(CentralMorphism:=(efunc_central a b)))).
  Defined.
  Coercion UnderlyingFunctor : EFunctor >-> Functor.

Class EBinoidalCat `(ec:ECategory) :=
{ ebc_bobj   :  ec -> ec -> ec
; ebc_first  :  forall a:ec, EFunctor ec ec (fun x => ebc_bobj x a)
; ebc_second :  forall a:ec, EFunctor ec ec (fun x => ebc_bobj a x)
; ebc_ec     := ec  (* this isn't a coercion - avoids duplicate paths *)
}.

Instance EBinoidalCat_is_binoidal `(ebc:EBinoidalCat(ec:=ec)) : BinoidalCat (Underlying ec) ebc_bobj.
  apply Build_BinoidalCat.
  apply (fun a => UnderlyingFunctor (ebc_first a)).
  apply (fun a => UnderlyingFunctor (ebc_second a)).
  Defined.

Coercion EBinoidalCat_is_binoidal : EBinoidalCat >-> BinoidalCat.

(* Enriched Fibrations *)
Section EFibration.

  Context `{E:ECategory}.
  Context  {Eob2}{Ehom2}{B:@ECategory Ob Hom V bin_obj' mn EI mn Eob2 Ehom2}.
  Context  {efobj}(F:EFunctor E B efobj).

  (*
   * A morphism is prone if its image factors through the image of
   * another morphism with the same codomain just in case the factor
   * is the image of a unique morphism.  One might say that it
   * "uniquely reflects factoring through morphisms with the same
   * codomain".
   *)
  Definition Prone {e e'}(φ:EI~~{V}~~>(e'~~>e)) :=
  forall e'' (ψ:EI~~{V}~~>(e''~~>e)) (g:(efobj e'')~~{B}~~>(efobj e')),
       (comp(Category:=B) _ _ _ g (φ >>> (efunc F _ _))) ~~
       ψ >>> (efunc F _ _)
   ->  { χ:e''~~{E}~~>e' & ψ ~~ χ >>> φ & g ~~ comp(Category:=V) _ _ _ χ (efunc F e'' e') }.
       (* FIXME: χ must also be unique *)

  (* a functor is a Street Fibration if morphisms with codomain in its image are, up to iso, the images of prone morphisms *)

  (* Street was the first to define non-evil fibrations using isomorphisms (for cleavage_pf below) rather than equality *)
  Structure StreetCleavage (e:E)(b:B)(f:b~~{B}~~>(efobj e)) :=
  { cleavage_e'   : E
  ; cleavage_pf   : (efobj cleavage_e') ≅ b
  ; cleavage_phi  : cleavage_e' ~~{E}~~> e
  ; cleavage_cart : Prone cleavage_phi
  ; cleavage_eqv  : #cleavage_pf >>> f  ~~ comp(Category:=V) _ _ _ cleavage_phi (efunc F _ _)
  }.

  (* if V, the category enriching E and B is V-enriched, we get a functor Bop->Vint *)

  (* Every equivalence of categories is a Street fibration *)

  (* this is actually a "Street Fibration", the non-evil version of a Grothendieck Fibration *)
  Definition EFibration := forall e b f, exists cl:StreetCleavage e b f, True.

  Definition ClovenEFibration := forall e b f, StreetCleavage e b f.

  (*
   * Now, a language has polymorphic types iff its category of
   * judgments contains a second enriched category, the category of
   * Kinds, and the category of types is fibered over the category of
   * Kinds, and the weakening functor-of-fibers has a right adjoint.
   *
   * http://ncatlab.org/nlab/show/Grothendieck+fibration
   *
   * I suppose we'll need to also ask that the R-functors takes
   * Prone morphisms to Prone morphisms.
   *)
End EFibration.

