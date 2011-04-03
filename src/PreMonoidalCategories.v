Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import InitialTerminal_ch2_2.
Require Import Subcategories_ch7_1.
Require Import NaturalTransformations_ch7_4.
Require Import NaturalIsomorphisms_ch7_5.
Require Import Coherence_ch7_8.
Require Import BinoidalCategories.

(* not in Awodey *)
Class PreMonoidalCat `(bc:BinoidalCat(C:=C))(I:C) :=
{ pmon_I               := I
; pmon_bin             := bc
; pmon_cat             := C
; pmon_assoc           : forall a b, (bin_second a >>>> bin_first b) <~~~> (bin_first b >>>> bin_second a)
; pmon_cancelr         :                               (bin_first I) <~~~> functor_id C
; pmon_cancell         :                              (bin_second I) <~~~> functor_id C
; pmon_pentagon        : Pentagon (fun a b c f => f ⋉ c) (fun a b c f => c ⋊ f) (fun a b c => #((pmon_assoc a c) b))
; pmon_triangle        : Triangle (fun a b c f => f ⋉ c) (fun a b c f => c ⋊ f) (fun a b c => #((pmon_assoc a c) b))
                                  (fun a => #(pmon_cancell a)) (fun a => #(pmon_cancelr a))
; pmon_assoc_rr        :  forall a b, (bin_first  (a⊗b)) <~~~> (bin_first  a >>>> bin_first  b)
; pmon_assoc_ll        :  forall a b, (bin_second (a⊗b)) <~~~> (bin_second b >>>> bin_second a)
; pmon_coherent_r      :  forall a c d:C,  #(pmon_assoc_rr c d a) ~~ #(pmon_assoc a d c)⁻¹
; pmon_coherent_l      :  forall a c d:C,  #(pmon_assoc_ll c a d) ~~ #(pmon_assoc c d a)
; pmon_assoc_central   :  forall a b c, CentralMorphism #(pmon_assoc   a b c)
; pmon_cancelr_central :  forall a    , CentralMorphism #(pmon_cancelr a)
; pmon_cancell_central :  forall a    , CentralMorphism #(pmon_cancell a)
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

Implicit Arguments pmon_cancell [ Ob Hom C bin_obj' bc I PreMonoidalCat ].
Implicit Arguments pmon_cancelr [ Ob Hom C bin_obj' bc I PreMonoidalCat ].
Implicit Arguments pmon_assoc   [ Ob Hom C bin_obj' bc I PreMonoidalCat ].
Coercion pmon_bin : PreMonoidalCat >-> BinoidalCat.

(* this turns out to be Exercise VII.1.1 from Mac Lane's CWM *)
Lemma MacLane_ex_VII_1_1 `{mn:PreMonoidalCat(I:=EI)} a b
  : #(pmon_cancelr (a ⊗ b)) ~~ #((pmon_assoc a EI) b) >>> (a ⋊-) \ #(pmon_cancelr b).
  set (pmon_pentagon EI EI a b) as penta. unfold pmon_pentagon in penta.
  set (pmon_triangle a b) as tria. unfold pmon_triangle in tria.
  apply (fmor_respects(bin_second EI)) in tria.
  set (@fmor_preserves_comp) as fpc.
  setoid_rewrite <- fpc in tria.
  set (ni_commutes (pmon_assoc a b)) as xx.
  (* FIXME *)
  Admitted.

Class PreMonoidalFunctor
`(PM1:PreMonoidalCat(C:=C1)(I:=I1))
`(PM2:PreMonoidalCat(C:=C2)(I:=I2))
 (fobj : C1 -> C2          ) :=
{ mf_F          :> Functor C1 C2 fobj
; mf_i          :  I2 ≅ mf_F I1
; mf_first      :  ∀ a,              mf_F >>>> bin_first  (mf_F a)  <~~~>  bin_first  a >>>> mf_F
; mf_second     :  ∀ a,              mf_F >>>> bin_second (mf_F a)  <~~~>  bin_second a >>>> mf_F
; mf_consistent :  ∀ a b,            #(mf_first a b) ~~ #(mf_second b a)
; mf_center     :  forall `(f:a~>b), CentralMorphism f -> CentralMorphism (mf_F \ f)
; mf_cancell    :  ∀ b,     #(pmon_cancell _) ~~ #mf_i ⋉ _ >>> #(mf_first  b I1) >>> mf_F \ #(pmon_cancell b)
; mf_cancelr    :  ∀ a,     #(pmon_cancelr _) ~~ _ ⋊ #mf_i >>> #(mf_second a I1) >>> mf_F \ #(pmon_cancelr a)
; mf_assoc      :  ∀ a b c, #(pmon_assoc _ _ _)  >>> _ ⋊ #(mf_second _ _) >>>        #(mf_second _ _) ~~
                            #(mf_second _ _) ⋉ _ >>>     #(mf_second _ _) >>> mf_F \ #(pmon_assoc a c b)
}.
Coercion mf_F : PreMonoidalFunctor >-> Functor.

Definition PreMonoidalFunctorsCompose
  `{PM1   :PreMonoidalCat(C:=C1)(I:=I1)}
  `{PM2   :PreMonoidalCat(C:=C2)(I:=I2)}
   {fobj12:C1 -> C2                    }
   (PMF12 :PreMonoidalFunctor PM1 PM2 fobj12)
  `{PM3   :PreMonoidalCat(C:=C3)(I:=I3)}
   {fobj23:C2 -> C3                    }
   (PMF23 :PreMonoidalFunctor PM2 PM3 fobj23)
   : PreMonoidalFunctor PM1 PM3 (fobj23 ○ fobj12).
   admit.
   Defined.

(*******************************************************************************)
(* Braided and Symmetric Categories                                            *)

Class BraidedCat `(mc:PreMonoidalCat) :=
{ br_niso        : forall a, bin_first a <~~~> bin_second a
; br_swap        := fun a b => ni_iso (br_niso b) a
; triangleb      : forall a:C,     #(pmon_cancelr a) ~~ #(br_swap a (pmon_I(PreMonoidalCat:=mc))) >>> #(pmon_cancell a)
; hexagon1       : forall {a b c}, #(pmon_assoc _ _ _) >>> #(br_swap a _) >>> #(pmon_assoc _ _ _)
                                   ~~ #(br_swap _ _) ⋉ c >>> #(pmon_assoc _ _ _) >>> b ⋊ #(br_swap _ _)
; hexagon2       : forall {a b c}, #(pmon_assoc _ _ _)⁻¹ >>> #(br_swap _ c) >>> #(pmon_assoc _ _ _)⁻¹
                                   ~~ a ⋊ #(br_swap _ _) >>> #(pmon_assoc _ _ _)⁻¹ >>> #(br_swap _ _) ⋉ b
}.

Class SymmetricCat `(bc:BraidedCat) :=
{ symcat_swap  :  forall a b:C, #((br_swap(BraidedCat:=bc)) a b) ~~ #(br_swap _ _)⁻¹
}.


Section PreMonoidalSubCategory.

  Context `(pm:PreMonoidalCat(I:=pmI)).
  Context  {Pobj}{Pmor}(S:SubCategory pm Pobj Pmor).
  Context  (Pobj_unit:Pobj pmI).
  Context  (Pobj_closed:forall {a}{b}, Pobj a -> Pobj b -> Pobj (a⊗b)).
  Implicit Arguments Pobj_closed [[a][b]].
  Context  (Pmor_first: forall {a}{b}{c}{f}(pa:Pobj a)(pb:Pobj b)(pc:Pobj c)(pf:Pmor _ _ pa pb f),
                            Pmor _ _ (Pobj_closed pa pc) (Pobj_closed pb pc) (f ⋉ c)).
  Context  (Pmor_second: forall {a}{b}{c}{f}(pa:Pobj a)(pb:Pobj b)(pc:Pobj c)(pf:Pmor _ _ pa pb f),
                            Pmor _ _ (Pobj_closed pc pa) (Pobj_closed pc pb) (c ⋊ f)).
  Context  (Pmor_assoc: forall {a}{b}{c}(pa:Pobj a)(pb:Pobj b)(pc:Pobj c),
                            Pmor _ _
                            (Pobj_closed (Pobj_closed pa pb) pc)
                            (Pobj_closed pa (Pobj_closed pb pc))
                            #(pmon_assoc a c b)).
  Context  (Pmor_unassoc: forall {a}{b}{c}(pa:Pobj a)(pb:Pobj b)(pc:Pobj c),
                            Pmor _ _
                            (Pobj_closed pa (Pobj_closed pb pc))
                            (Pobj_closed (Pobj_closed pa pb) pc)
                            #(pmon_assoc a c b)⁻¹).
  Context  (Pmor_cancell: forall {a}(pa:Pobj a),
                            Pmor _ _ (Pobj_closed Pobj_unit pa) pa 
                            #(pmon_cancell a)).
  Context  (Pmor_uncancell: forall {a}(pa:Pobj a),
                            Pmor _ _ pa (Pobj_closed Pobj_unit pa)
                            #(pmon_cancell a)⁻¹).
  Context  (Pmor_cancelr: forall {a}(pa:Pobj a),
                            Pmor _ _ (Pobj_closed pa Pobj_unit) pa 
                            #(pmon_cancelr a)).
  Context  (Pmor_uncancelr: forall {a}(pa:Pobj a),
                            Pmor _ _ pa (Pobj_closed pa Pobj_unit)
                            #(pmon_cancelr a)⁻¹).
  Implicit Arguments Pmor_first [[a][b][c][f]].
  Implicit Arguments Pmor_second [[a][b][c][f]].

  Definition PreMonoidalSubCategory_bobj (x y:S) :=
    existT Pobj _ (Pobj_closed (projT2 x) (projT2 y)).

  Definition PreMonoidalSubCategory_first_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y),
    (PreMonoidalSubCategory_bobj x a)~~{S}~~>(PreMonoidalSubCategory_bobj y a).
    unfold hom; simpl; intros.
    destruct f.
    destruct a as [a apf].
    destruct x as [x xpf].
    destruct y as [y ypf].
    simpl in *.
    exists (x0 ⋉ a).
    apply Pmor_first; auto.
    Defined.

  Definition PreMonoidalSubCategory_second_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y),
    (PreMonoidalSubCategory_bobj a x)~~{S}~~>(PreMonoidalSubCategory_bobj a y).
    unfold hom; simpl; intros.
    destruct f.
    destruct a as [a apf].
    destruct x as [x xpf].
    destruct y as [y ypf].
    simpl in *.
    exists (a ⋊ x0).
    apply Pmor_second; auto.
    Defined.

  Instance PreMonoidalSubCategory_first (a:S)
    : Functor (S) (S) (fun x => PreMonoidalSubCategory_bobj x a) :=
    { fmor := fun x y f => PreMonoidalSubCategory_first_fmor a f }.
    unfold PreMonoidalSubCategory_first_fmor; intros; destruct a; destruct a0; destruct b; destruct f; destruct f'; simpl in *.
    apply (fmor_respects (-⋉x)); auto.
    unfold PreMonoidalSubCategory_first_fmor; intros; destruct a; destruct a0;  simpl in *.
    apply (fmor_preserves_id (-⋉x)); auto.
    unfold PreMonoidalSubCategory_first_fmor; intros;
      destruct a; destruct a0; destruct b; destruct c; destruct f; destruct g; simpl in *.
    apply (fmor_preserves_comp (-⋉x)); auto.
    Defined.

  Instance PreMonoidalSubCategory_second (a:S)
    : Functor (S) (S) (fun x => PreMonoidalSubCategory_bobj a x) :=
    { fmor := fun x y f => PreMonoidalSubCategory_second_fmor a f }.
    unfold PreMonoidalSubCategory_second_fmor; intros; destruct a; destruct a0; destruct b; destruct f; destruct f'; simpl in *.
    apply (fmor_respects (x⋊-)); auto.
    unfold PreMonoidalSubCategory_second_fmor; intros; destruct a; destruct a0;  simpl in *.
    apply (fmor_preserves_id (x⋊-)); auto.
    unfold PreMonoidalSubCategory_second_fmor; intros;
      destruct a; destruct a0; destruct b; destruct c; destruct f; destruct g; simpl in *.
    apply (fmor_preserves_comp (x⋊-)); auto.
    Defined.

  Instance PreMonoidalSubCategory_is_Binoidal : BinoidalCat S PreMonoidalSubCategory_bobj :=
    { bin_first := PreMonoidalSubCategory_first
    ; bin_second := PreMonoidalSubCategory_second }.

  Definition PreMonoidalSubCategory_assoc
    : forall a b,
      (PreMonoidalSubCategory_second a >>>> PreMonoidalSubCategory_first b) <~~~>
      (PreMonoidalSubCategory_first  b >>>> PreMonoidalSubCategory_second a).
    admit.
    Defined.

  Definition PreMonoidalSubCategory_assoc_ll
    : forall a b,
      PreMonoidalSubCategory_second (a⊗b) <~~~>
      PreMonoidalSubCategory_second b >>>> PreMonoidalSubCategory_second a.
    intros.
    admit.
    Defined.

  Definition PreMonoidalSubCategory_assoc_rr
    : forall a b,
      PreMonoidalSubCategory_first (a⊗b) <~~~>
      PreMonoidalSubCategory_first a >>>> PreMonoidalSubCategory_first b.
    intros.
    admit.
    Defined.

  Definition PreMonoidalSubCategory_I := existT _ pmI (Pobj_unit).

  Definition PreMonoidalSubCategory_cancelr : PreMonoidalSubCategory_first PreMonoidalSubCategory_I <~~~> functor_id _.
    admit.
    Defined.

  Definition PreMonoidalSubCategory_cancell : PreMonoidalSubCategory_second PreMonoidalSubCategory_I <~~~> functor_id _.
    admit.
    Defined.

  Instance PreMonoidalSubCategory_PreMonoidal : PreMonoidalCat PreMonoidalSubCategory_is_Binoidal PreMonoidalSubCategory_I :=
  { pmon_assoc           := PreMonoidalSubCategory_assoc 
  ; pmon_assoc_rr        := PreMonoidalSubCategory_assoc_rr
  ; pmon_assoc_ll        := PreMonoidalSubCategory_assoc_ll
  ; pmon_cancelr         := PreMonoidalSubCategory_cancelr
  ; pmon_cancell         := PreMonoidalSubCategory_cancell
  }.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  Defined.

End PreMonoidalSubCategory.
