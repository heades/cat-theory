Generalizable All Variables.
Require Import Preamble.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import EpicMonic_ch2_1.
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
Lemma MacLane_ex_VII_1_1 `{mn:PreMonoidalCat(I:=EI)} b a
  : 
  let    α := fun a b c => #((pmon_assoc a c) b)
  in     α a b EI >>> _ ⋊ #(pmon_cancelr _) ~~ #(pmon_cancelr _).

  intros.  simpl in α.

  (* following Mac Lane's hint, we aim for (λ >>> α >>> λ×1)~~(λ >>> λ) *)
  set (epic _ (iso_epic (pmon_cancelr ((a⊗b)⊗EI)))) as q.
    apply q.
    clear q.

  (* next, we show that the hint goal above is implied by the bottom-left 1/5th of the big whiteboard diagram *)
  set (ni_commutes pmon_cancelr (α a b EI)) as q.
    setoid_rewrite <- associativity.
    setoid_rewrite q.
    clear q.
    setoid_rewrite associativity.

    set (ni_commutes pmon_cancelr (a ⋊ #(pmon_cancelr b))) as q.
    simpl in q.
    setoid_rewrite q.
    clear q.

    set (ni_commutes pmon_cancelr (#(pmon_cancelr (a⊗b)))) as q.
    simpl in q.
    setoid_rewrite q.
    clear q.

    setoid_rewrite <- associativity.
    apply comp_respects; try reflexivity.

  (* now we carry out the proof in the whiteboard diagram, starting from the pentagon diagram *)

  (* top 2/5ths *)
  assert (α (a⊗b) EI EI >>> α _ _ _ >>> (_ ⋊ (_ ⋊ #(pmon_cancell _))) ~~ #(pmon_cancelr _) ⋉ _ >>> α _ _ _).
    set (pmon_triangle (a⊗b) EI) as tria.
    simpl in tria.
    unfold α; simpl.
    setoid_rewrite tria.
    clear tria.
    setoid_rewrite associativity.
    apply comp_respects; try reflexivity.
    set (ni_commutes (pmon_assoc_ll a b) #(pmon_cancell EI)) as x.
    simpl in x.
    setoid_rewrite pmon_coherent_l in x.
    apply x.

  (* bottom 3/5ths *)
  assert (((#((pmon_assoc a EI) b) ⋉ EI >>> #((pmon_assoc a EI) (b ⊗ EI))) >>>
    a ⋊ #((pmon_assoc b EI) EI)) >>> a ⋊ (b ⋊ #(pmon_cancell EI))
    ~~ α _ _ _ ⋉ _ >>> (_ ⋊ #(pmon_cancelr _)) ⋉ _ >>> α _ _ _).

    unfold α; simpl.
    repeat setoid_rewrite associativity.
    apply comp_respects; try reflexivity.

    set (ni_commutes (pmon_assoc a EI) (#(pmon_cancelr b) )) as x.
    simpl in x.
    setoid_rewrite <- associativity.
    simpl in x.
    setoid_rewrite <- x.
    clear x.

    setoid_rewrite associativity.
    apply comp_respects; try reflexivity.
    setoid_rewrite (fmor_preserves_comp (a⋊-)).
    apply (fmor_respects (a⋊-)).

    set (pmon_triangle b EI) as tria.
    simpl in tria.
    symmetry.
    apply tria.

  set (pmon_pentagon a b EI EI) as penta. unfold pmon_pentagon in penta. simpl in penta.

  set (@comp_respects _ _ _ _ _ _ _ _ penta (a ⋊ (b ⋊ #(pmon_cancell EI))) (a ⋊ (b ⋊ #(pmon_cancell EI)))) as qq.
    unfold α in H.
    setoid_rewrite H in qq.
    unfold α in H0.
    setoid_rewrite H0 in qq.
    clear H0 H.

  unfold α.
    apply (monic _ (iso_monic ((pmon_assoc a EI) b))).
    apply qq.
    clear qq penta.
    reflexivity.
    Qed.

Class PreMonoidalFunctor
`(PM1:PreMonoidalCat(C:=C1)(I:=I1))
`(PM2:PreMonoidalCat(C:=C2)(I:=I2))
 (fobj : C1 -> C2                 ) :=
{ mf_F          :> Functor C1 C2 fobj
; mf_i          :  I2 ≅ mf_F I1
; mf_first      :  ∀ a,              mf_F >>>> bin_first  (mf_F a)  <~~~>  bin_first  a >>>> mf_F
; mf_second     :  ∀ a,              mf_F >>>> bin_second (mf_F a)  <~~~>  bin_second a >>>> mf_F
; mf_consistent :  ∀ a b,            #(mf_first a b) ~~ #(mf_second b a)
; mf_center     :  forall `(f:a~>b), CentralMorphism f -> CentralMorphism (mf_F \ f)
; mf_cancell    :  ∀ b,     #(pmon_cancell _) ~~ #mf_i ⋉ _ >>> #(mf_first  b I1) >>> mf_F \ #(pmon_cancell b)
; mf_cancelr    :  ∀ a,     #(pmon_cancelr _) ~~ _ ⋊ #mf_i >>> #(mf_second a I1) >>> mf_F \ #(pmon_cancelr a)
; mf_assoc      :  ∀ a b c, #(pmon_assoc _ _ _)  >>> _ ⋊ #(mf_first _ _) >>>        #(mf_second _ _) ~~
                            #(mf_second _ _) ⋉ _  >>>     #(mf_first _ _) >>> mf_F \ #(pmon_assoc a c b)
}.
Coercion mf_F : PreMonoidalFunctor >-> Functor.

Section PreMonoidalFunctorsCompose.
  Context
  `{PM1   :PreMonoidalCat(C:=C1)(I:=I1)}
  `{PM2   :PreMonoidalCat(C:=C2)(I:=I2)}
   {fobj12:C1 -> C2                    }
   (PMF12 :PreMonoidalFunctor PM1 PM2 fobj12)
  `{PM3   :PreMonoidalCat(C:=C3)(I:=I3)}
   {fobj23:C2 -> C3                    }
   (PMF23 :PreMonoidalFunctor PM2 PM3 fobj23).

  Definition compose_mf := PMF12 >>>> PMF23.

  Definition compose_mf_i : I3 ≅ PMF23 (PMF12 I1).
    eapply iso_comp.
    apply (mf_i(PreMonoidalFunctor:=PMF23)).
    apply functors_preserve_isos.
    apply (mf_i(PreMonoidalFunctor:=PMF12)).
    Defined.

  Definition compose_mf_first a : compose_mf >>>> bin_first (compose_mf a)  <~~~>  bin_first  a >>>> compose_mf.
    set (mf_first(PreMonoidalFunctor:=PMF12) a) as mf_first12.
    set (mf_first(PreMonoidalFunctor:=PMF23) (PMF12 a)) as mf_first23.
    unfold functor_fobj in *; simpl in *.
    unfold compose_mf.
    eapply ni_comp.
    apply (ni_associativity PMF12 PMF23 (- ⋉fobj23 (fobj12 a))).
    eapply ni_comp.
    apply (ni_respects1 PMF12 (PMF23 >>>> - ⋉fobj23 (fobj12 a)) (- ⋉fobj12 a >>>> PMF23)).
    apply mf_first23.
    clear mf_first23.

    eapply ni_comp.
    eapply ni_inv.
    apply (ni_associativity PMF12 (- ⋉fobj12 a) PMF23).

    apply ni_inv.
    eapply ni_comp.
    eapply ni_inv.
    eapply (ni_associativity _ PMF12 PMF23).

    apply ni_respects2.
    apply ni_inv.
    apply mf_first12.
    Defined.
    
  Definition compose_mf_second a : compose_mf >>>> bin_second (compose_mf a)  <~~~>  bin_second  a >>>> compose_mf.
    set (mf_second(PreMonoidalFunctor:=PMF12) a) as mf_second12.
    set (mf_second(PreMonoidalFunctor:=PMF23) (PMF12 a)) as mf_second23.
    unfold functor_fobj in *; simpl in *.
    unfold compose_mf.
    eapply ni_comp.
    apply (ni_associativity PMF12 PMF23 (fobj23 (fobj12 a) ⋊-)).
    eapply ni_comp.
    apply (ni_respects1 PMF12 (PMF23 >>>> fobj23 (fobj12 a) ⋊-) (fobj12 a ⋊- >>>> PMF23)).
    apply mf_second23.
    clear mf_second23.

    eapply ni_comp.
    eapply ni_inv.
    apply (ni_associativity PMF12 (fobj12 a ⋊ -) PMF23).

    apply ni_inv.
    eapply ni_comp.
    eapply ni_inv.
    eapply (ni_associativity (a ⋊-) PMF12 PMF23).

    apply ni_respects2.
    apply ni_inv.
    apply mf_second12.
    Defined.

  (* this proof is really gross; I will write a better one some other day *)
  Lemma mf_associativity_comp :
   ∀a b c : C1,
   (#((pmon_assoc (compose_mf a) (compose_mf c)) (fobj23 (fobj12 b))) >>>
    compose_mf a ⋊ #((compose_mf_first c) b)) >>>
   #((compose_mf_second a) (b ⊗ c)) ~~
   (#((compose_mf_second a) b) ⋉ compose_mf c >>>
    #((compose_mf_first c) (a ⊗ b))) >>> compose_mf \ #((pmon_assoc a c) b).
    intros; intros.
      unfold compose_mf_second; simpl.
      unfold compose_mf_first; simpl.
      unfold functor_comp; simpl.
      unfold ni_respects1.
      unfold functor_fobj; simpl.
      
      set (mf_first (fobj12 c)) as m'.
      assert (mf_first (fobj12 c)=m'). reflexivity.
      destruct m'; simpl.

      set (mf_second (fobj12 a)) as m.
      assert (mf_second (fobj12 a)=m). reflexivity.
      destruct m; simpl.

      Implicit Arguments id [[Ob][Hom][Category][a]].
      idtac.

      symmetry.
      etransitivity.
      repeat setoid_rewrite <- fmor_preserves_comp.
      repeat setoid_rewrite fmor_preserves_id.
      repeat setoid_rewrite left_identity.
      repeat setoid_rewrite right_identity.
      reflexivity.
      symmetry.
      etransitivity.
      repeat setoid_rewrite <- fmor_preserves_comp.
      repeat setoid_rewrite fmor_preserves_id.
      repeat setoid_rewrite left_identity.
      repeat setoid_rewrite right_identity.
      reflexivity.

      assert (   (#((pmon_assoc (fobj23 (fobj12 a)) (fobj23 (fobj12 c)))
              (fobj23 (fobj12 b))) >>>
          fobj23 (fobj12 a)
          ⋊ (
             (#(ni_iso (fobj12 b)) >>> ( (PMF23 \ #((mf_first c) b) ))))) >>>
         (
          (#(ni_iso0 (fobj12 (b ⊗ c))) >>>
           ((PMF23 \ #((mf_second a) (b ⊗ c)))))) ~~
         ((
           (#(ni_iso0 (fobj12 b)) >>> ( (PMF23 \ #((mf_second a) b) ))))
          ⋉ fobj23 (fobj12 c) >>>
          (
           (#(ni_iso (fobj12 (a ⊗ b))) >>>
            ( (PMF23 \ #((mf_first c) (a ⊗ b))))))) >>>
         PMF23 \ (PMF12 \ #((pmon_assoc a c) b))
      ).

      repeat setoid_rewrite associativity.
      setoid_rewrite (fmor_preserves_comp PMF23).
            unfold functor_comp in *.
            unfold functor_fobj in *.
            simpl in *.
            rename ni_commutes into ni_commutes7.
      set (mf_assoc(PreMonoidalFunctor:=PMF12)) as q.
      set (ni_commutes7 _ _ (#((mf_second a) b))) as q'.
      simpl in q'.
      repeat setoid_rewrite associativity.
      symmetry.
      setoid_rewrite <- (fmor_preserves_comp (-⋉ fobj23 (fobj12 c))).
      repeat setoid_rewrite <- associativity.
      setoid_rewrite juggle1.
      setoid_rewrite <- q'.
      repeat setoid_rewrite associativity.
      setoid_rewrite fmor_preserves_comp.
      idtac.
      unfold functor_fobj in *.
      simpl in *.
      repeat setoid_rewrite <- associativity.
      setoid_rewrite <- q.
      clear q.
      repeat setoid_rewrite <- fmor_preserves_comp.
      repeat setoid_rewrite <- associativity.
      apply comp_respects; try reflexivity.
      
      set (mf_assoc(PreMonoidalFunctor:=PMF23) (fobj12 a) (fobj12 b) (fobj12 c)) as q.
      unfold functor_fobj in *.
      simpl in *.
      
      rewrite H in q.
      rewrite H0 in q.
      simpl in q.
      repeat setoid_rewrite <- associativity.
      repeat setoid_rewrite <- associativity in q.
      setoid_rewrite <- q.
      clear q.
      unfold functor_fobj; simpl.
      
      repeat setoid_rewrite associativity.
      apply comp_respects; try reflexivity.
      apply comp_respects; try reflexivity.
      auto.
      
      repeat setoid_rewrite associativity.
      repeat setoid_rewrite associativity in H1.
      repeat setoid_rewrite <- fmor_preserves_comp in H1.
      repeat setoid_rewrite associativity in H1.
      apply H1.
      Qed.
      Implicit Arguments id [[Ob][Hom][Category]].

  (* this proof is really gross; I will write a better one some other day *)
  Instance PreMonoidalFunctorsCompose : PreMonoidalFunctor PM1 PM3 (fobj23 ○ fobj12) :=
  { mf_i      := compose_mf_i
  ; mf_F      := compose_mf
  ; mf_first  := compose_mf_first  
  ; mf_second := compose_mf_second }.

    intros; unfold compose_mf_first; unfold compose_mf_second.
      set (mf_first (PMF12 a)) as x in *.
      set (mf_second (PMF12 b)) as y in *.
      assert (x=mf_first (PMF12 a)). reflexivity.
      assert (y=mf_second (PMF12 b)). reflexivity.
      destruct x.
      destruct y.
      simpl.
      repeat setoid_rewrite left_identity.
      repeat setoid_rewrite right_identity.
      set (mf_consistent (PMF12 a) (PMF12 b)) as later.
      apply comp_respects; try reflexivity.
      rewrite <- H in later.
      rewrite <- H0 in later.
      simpl in later.
      apply later.
      apply fmor_respects.
      apply mf_consistent.

    intros.
      simpl.
      apply mf_center.
      apply mf_center.
      auto.

    intros.
      unfold compose_mf_first; simpl.
      set (mf_first (PMF12 b)) as m.
      assert (mf_first (PMF12 b)=m). reflexivity.
      destruct m.
      simpl.
      unfold functor_fobj; simpl.
      repeat setoid_rewrite <- fmor_preserves_comp.
      repeat setoid_rewrite left_identity.
      repeat setoid_rewrite right_identity.

      set (mf_cancell b) as y.
      set (mf_cancell (fobj12 b)) as y'.
      unfold functor_fobj in *.
      setoid_rewrite y in y'.
      clear y.
      setoid_rewrite <- fmor_preserves_comp in y'.
      setoid_rewrite <- fmor_preserves_comp in y'.
      etransitivity.
      apply y'.
      clear y'.

      repeat setoid_rewrite <- associativity.
      apply comp_respects; try reflexivity.
      apply comp_respects; try reflexivity.
      repeat setoid_rewrite associativity.
      apply comp_respects; try reflexivity.

      set (ni_commutes _ _ #mf_i) as x.
      unfold functor_comp in x.
      unfold functor_fobj in x.
      simpl in x.
      rewrite H.
      simpl.
      apply x.

    intros.
      unfold compose_mf_second; simpl.
      set (mf_second (PMF12 a)) as m.
      assert (mf_second (PMF12 a)=m). reflexivity.
      destruct m.
      simpl.
      unfold functor_fobj; simpl.
      repeat setoid_rewrite <- fmor_preserves_comp.
      repeat setoid_rewrite left_identity.
      repeat setoid_rewrite right_identity.

      set (mf_cancelr a) as y.
      set (mf_cancelr (fobj12 a)) as y'.
      unfold functor_fobj in *.
      setoid_rewrite y in y'.
      clear y.
      setoid_rewrite <- fmor_preserves_comp in y'.
      setoid_rewrite <- fmor_preserves_comp in y'.
      etransitivity.
      apply y'.
      clear y'.

      repeat setoid_rewrite <- associativity.
      apply comp_respects; try reflexivity.
      apply comp_respects; try reflexivity.
      repeat setoid_rewrite associativity.
      apply comp_respects; try reflexivity.

      set (ni_commutes _ _ #mf_i) as x.
      unfold functor_comp in x.
      unfold functor_fobj in x.
      simpl in x.
      rewrite H.
      simpl.
      apply x.

    apply mf_associativity_comp.

      Defined.

End PreMonoidalFunctorsCompose.


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


(* a wide subcategory inherits the premonoidal structure if it includes all of the coherence maps *)
Section PreMonoidalWideSubcategory.

  Context `(pm:PreMonoidalCat(I:=pmI)).
  Context  {Pmor}(S:WideSubcategory pm Pmor).
  Context  (Pmor_first  : forall {a}{b}{c}{f}(pf:Pmor a b f), Pmor _ _ (f ⋉ c)).
  Context  (Pmor_second : forall {a}{b}{c}{f}(pf:Pmor a b f), Pmor _ _ (c ⋊ f)).
  Context  (Pmor_assoc  : forall {a}{b}{c}, Pmor _ _ #(pmon_assoc a c b)).
  Context  (Pmor_unassoc: forall {a}{b}{c}, Pmor _ _ #(pmon_assoc a c b)⁻¹).
  Context  (Pmor_cancell: forall {a}, Pmor _ _ #(pmon_cancell a)).
  Context  (Pmor_uncancell: forall {a}, Pmor _ _ #(pmon_cancell a)⁻¹).
  Context  (Pmor_cancelr: forall {a}, Pmor _ _ #(pmon_cancelr a)).
  Context  (Pmor_uncancelr: forall {a}, Pmor _ _ #(pmon_cancelr a)⁻¹).
  Implicit Arguments Pmor_first [[a][b][c][f]].
  Implicit Arguments Pmor_second [[a][b][c][f]].

  Definition PreMonoidalWideSubcategory_first_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y), (bin_obj' x a)~~{S}~~>(bin_obj' y a).
    unfold hom; simpl; intros.
    destruct f.
    simpl in *.
    exists (bin_first(BinoidalCat:=pm) a \ x0).
    apply Pmor_first; auto.
    Defined.

  Definition PreMonoidalWideSubcategory_second_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y), (bin_obj' a x)~~{S}~~>(bin_obj' a y).
    unfold hom; simpl; intros.
    destruct f.
    simpl in *.
    exists (bin_second(BinoidalCat:=pm) a \ x0).
    apply Pmor_second; auto.
    Defined.

  Instance PreMonoidalWideSubcategory_first (a:S) : Functor S S (fun x => bin_obj' x a) :=
    { fmor := fun x y f => PreMonoidalWideSubcategory_first_fmor a f }.
    unfold PreMonoidalWideSubcategory_first_fmor; intros; destruct f; destruct f'; simpl in *.
    apply (fmor_respects (bin_first(BinoidalCat:=pm) a)); auto.
    unfold PreMonoidalWideSubcategory_first_fmor; intros; simpl in *.
    apply (fmor_preserves_id (bin_first(BinoidalCat:=pm) a)); auto.
    unfold PreMonoidalWideSubcategory_first_fmor; intros; destruct f; destruct g; simpl in *.
    apply (fmor_preserves_comp (bin_first(BinoidalCat:=pm) a)); auto.
    Defined.

  Instance PreMonoidalWideSubcategory_second (a:S) : Functor S S (fun x => bin_obj' a x) :=
    { fmor := fun x y f => PreMonoidalWideSubcategory_second_fmor a f }.
    unfold PreMonoidalWideSubcategory_second_fmor; intros; destruct f; destruct f'; simpl in *.
    apply (fmor_respects (bin_second(BinoidalCat:=pm) a)); auto.
    unfold PreMonoidalWideSubcategory_second_fmor; intros; simpl in *.
    apply (fmor_preserves_id (bin_second(BinoidalCat:=pm) a)); auto.
    unfold PreMonoidalWideSubcategory_second_fmor; intros; destruct f; destruct g; simpl in *.
    apply (fmor_preserves_comp (bin_second(BinoidalCat:=pm) a)); auto.
    Defined.

  Instance PreMonoidalWideSubcategory_is_Binoidal : BinoidalCat S bin_obj' :=
    { bin_first  := PreMonoidalWideSubcategory_first
    ; bin_second := PreMonoidalWideSubcategory_second }.

  Definition PreMonoidalWideSubcategory_assoc_iso
    : forall a b c, Isomorphic(C:=S) (bin_obj' (bin_obj' a b) c) (bin_obj' a (bin_obj' b c)).
    intros.
    refine {| iso_forward := existT _ _ (Pmor_assoc a b c) ; iso_backward := existT _ _ (Pmor_unassoc a b c) |}.
    simpl; apply iso_comp1.
    simpl; apply iso_comp2.
    Defined.

  Definition PreMonoidalWideSubcategory_assoc
    : forall a b,
      (PreMonoidalWideSubcategory_second a >>>> PreMonoidalWideSubcategory_first b) <~~~>
      (PreMonoidalWideSubcategory_first  b >>>> PreMonoidalWideSubcategory_second a).
    intros.
    apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _ (PreMonoidalWideSubcategory_second a >>>>
      PreMonoidalWideSubcategory_first b) (PreMonoidalWideSubcategory_first b >>>>
        PreMonoidalWideSubcategory_second a) (fun c => PreMonoidalWideSubcategory_assoc_iso a c b)).
    intros; simpl.
    unfold PreMonoidalWideSubcategory_second_fmor; simpl.
    destruct f; simpl.
    set (ni_commutes (pmon_assoc(PreMonoidalCat:=pm) a b) x) as q.
    apply q.
    Defined.

  Definition PreMonoidalWideSubcategory_assoc_ll
    : forall a b,
      PreMonoidalWideSubcategory_second (a⊗b) <~~~>
      PreMonoidalWideSubcategory_second b >>>> PreMonoidalWideSubcategory_second a.
    intros.
    apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _
             (PreMonoidalWideSubcategory_second (a⊗b))
             (PreMonoidalWideSubcategory_second b >>>> PreMonoidalWideSubcategory_second a)
             (fun c => PreMonoidalWideSubcategory_assoc_iso a b c)).
    intros; simpl.
    unfold PreMonoidalWideSubcategory_second_fmor; simpl.
    destruct f; simpl.
    set (ni_commutes (pmon_assoc_ll(PreMonoidalCat:=pm) a b) x) as q.
    unfold functor_comp in q; simpl in q.
    set (pmon_coherent_l(PreMonoidalCat:=pm)) as q'.
    setoid_rewrite q' in q.
    apply q.
    Defined.

  Definition PreMonoidalWideSubcategory_assoc_rr
    : forall a b,
      PreMonoidalWideSubcategory_first (a⊗b) <~~~>
      PreMonoidalWideSubcategory_first a >>>> PreMonoidalWideSubcategory_first b.
    intros.
    apply ni_inv.
    apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _
             (PreMonoidalWideSubcategory_first a >>>> PreMonoidalWideSubcategory_first b)
             (PreMonoidalWideSubcategory_first (a⊗b))
             (fun c => PreMonoidalWideSubcategory_assoc_iso c a b)).
    intros; simpl.
    unfold PreMonoidalWideSubcategory_second_fmor; simpl.
    destruct f; simpl.
    set (ni_commutes (pmon_assoc_rr(PreMonoidalCat:=pm) a b) x) as q.
    unfold functor_comp in q; simpl in q.
    set (pmon_coherent_r(PreMonoidalCat:=pm)) as q'.
    setoid_rewrite q' in q.
    apply iso_shift_right' in q.
    apply iso_shift_left.
    symmetry.
    setoid_rewrite iso_inv_inv in q.
    setoid_rewrite associativity.
    apply q.
    Defined.

  Definition PreMonoidalWideSubcategory_cancelr_iso : forall a, Isomorphic(C:=S) (bin_obj' a pmI) a.
    intros.
    refine {| iso_forward := existT _ _ (Pmor_cancelr a) ; iso_backward := existT _ _ (Pmor_uncancelr a) |}.
    simpl; apply iso_comp1.
    simpl; apply iso_comp2.
    Defined.

  Definition PreMonoidalWideSubcategory_cancell_iso : forall a, Isomorphic(C:=S) (bin_obj' pmI a) a.
    intros.
    refine {| iso_forward := existT _ _ (Pmor_cancell a) ; iso_backward := existT _ _ (Pmor_uncancell a) |}.
    simpl; apply iso_comp1.
    simpl; apply iso_comp2.
    Defined.

  Definition PreMonoidalWideSubcategory_cancelr : PreMonoidalWideSubcategory_first pmI <~~~> functor_id _.
    apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _
             (PreMonoidalWideSubcategory_first pmI) (functor_id _) PreMonoidalWideSubcategory_cancelr_iso).
    intros; simpl.
    unfold PreMonoidalWideSubcategory_first_fmor; simpl.
    destruct f; simpl.
    apply (ni_commutes (pmon_cancelr(PreMonoidalCat:=pm)) x).
    Defined.

  Definition PreMonoidalWideSubcategory_cancell : PreMonoidalWideSubcategory_second pmI <~~~> functor_id _.
    apply (@Build_NaturalIsomorphism _ _ _ _ _ _ _ _
             (PreMonoidalWideSubcategory_second pmI) (functor_id _) PreMonoidalWideSubcategory_cancell_iso).
    intros; simpl.
    unfold PreMonoidalWideSubcategory_second_fmor; simpl.
    destruct f; simpl.
    apply (ni_commutes (pmon_cancell(PreMonoidalCat:=pm)) x).
    Defined.

  Instance PreMonoidalWideSubcategory_PreMonoidal : PreMonoidalCat PreMonoidalWideSubcategory_is_Binoidal pmI :=
  { pmon_assoc           := PreMonoidalWideSubcategory_assoc 
  ; pmon_assoc_rr        := PreMonoidalWideSubcategory_assoc_rr
  ; pmon_assoc_ll        := PreMonoidalWideSubcategory_assoc_ll
  ; pmon_cancelr         := PreMonoidalWideSubcategory_cancelr
  ; pmon_cancell         := PreMonoidalWideSubcategory_cancell
  }.
  apply Build_Pentagon.
    intros; unfold PreMonoidalWideSubcategory_assoc; simpl.
    set (pmon_pentagon(PreMonoidalCat:=pm) a b c) as q.
    simpl in q.
    apply q.
  apply Build_Triangle.
    intros; unfold PreMonoidalWideSubcategory_assoc;
      unfold PreMonoidalWideSubcategory_cancelr; unfold PreMonoidalWideSubcategory_cancell; simpl.
    set (pmon_triangle(PreMonoidalCat:=pm) a b) as q.
    simpl in q.
    apply q.
    intros.

  set (pmon_triangle(PreMonoidalCat:=pm)) as q.
    apply q.

  intros; simpl; reflexivity.
  intros; simpl; reflexivity.

  intros; simpl.
    apply Build_CentralMorphism; intros; simpl; destruct g; simpl.
    apply (pmon_assoc_central(PreMonoidalCat:=pm) a b c).
    apply (pmon_assoc_central(PreMonoidalCat:=pm) a b c).

  intros; simpl.
    apply Build_CentralMorphism; intros; simpl; destruct g; simpl.
    apply (pmon_cancelr_central(PreMonoidalCat:=pm) a).
    apply (pmon_cancelr_central(PreMonoidalCat:=pm) a).

  intros; simpl.
    apply Build_CentralMorphism; intros; simpl; destruct g; simpl.
    apply (pmon_cancell_central(PreMonoidalCat:=pm) a).
    apply (pmon_cancell_central(PreMonoidalCat:=pm) a).
    Defined.

End PreMonoidalWideSubcategory.


(* a full subcategory inherits the premonoidal structure if it includes the unit object and is closed under object-pairing *)
(*
Section PreMonoidalFullSubcategory.

  Context `(pm:PreMonoidalCat(I:=pmI)).
  Context  {Pobj}(S:FullSubcategory pm Pobj).
  Context  (Pobj_unit:Pobj pmI).
  Context  (Pobj_closed:forall {a}{b}, Pobj a -> Pobj b -> Pobj (a⊗b)).
  Implicit Arguments Pobj_closed [[a][b]].

  Definition PreMonoidalFullSubcategory_bobj (x y:S) :=
    existT Pobj _ (Pobj_closed (projT2 x) (projT2 y)).

  Definition PreMonoidalFullSubcategory_first_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y),
    (PreMonoidalFullSubcategory_bobj x a)~~{S}~~>(PreMonoidalFullSubcategory_bobj y a).
    unfold hom; simpl; intros.
    destruct a as [a apf].
    destruct x as [x xpf].
    destruct y as [y ypf].
    simpl in *.
    apply (f ⋉ a).
    Defined.

  Definition PreMonoidalFullSubcategory_second_fmor (a:S) : forall {x}{y}(f:x~~{S}~~>y),
    (PreMonoidalFullSubcategory_bobj a x)~~{S}~~>(PreMonoidalFullSubcategory_bobj a y).
    unfold hom; simpl; intros.
    destruct a as [a apf].
    destruct x as [x xpf].
    destruct y as [y ypf].
    simpl in *.
    apply (a ⋊ f).
    Defined.

  Instance PreMonoidalFullSubcategory_first (a:S)
    : Functor S S (fun x => PreMonoidalFullSubcategory_bobj x a) :=
    { fmor := fun x y f => PreMonoidalFullSubcategory_first_fmor a f }.
    unfold PreMonoidalFullSubcategory_first_fmor; intros; destruct a; destruct a0; destruct b; simpl in *.
    apply (fmor_respects (-⋉x)); auto.
    unfold PreMonoidalFullSubcategory_first_fmor; intros; destruct a; destruct a0;  simpl in *.
    apply (fmor_preserves_id (-⋉x)); auto.
    unfold PreMonoidalFullSubcategory_first_fmor; intros;
      destruct a; destruct a0; destruct b; destruct c; simpl in *.
    apply (fmor_preserves_comp (-⋉x)); auto.
    Defined.

  Instance PreMonoidalFullSubcategory_second (a:S)
    : Functor S S (fun x => PreMonoidalFullSubcategory_bobj a x) :=
    { fmor := fun x y f => PreMonoidalFullSubcategory_second_fmor a f }.
    unfold PreMonoidalFullSubcategory_second_fmor; intros; destruct a; destruct a0; destruct b; simpl in *.
    apply (fmor_respects (x⋊-)); auto.
    unfold PreMonoidalFullSubcategory_second_fmor; intros; destruct a; destruct a0;  simpl in *.
    apply (fmor_preserves_id (x⋊-)); auto.
    unfold PreMonoidalFullSubcategory_second_fmor; intros;
      destruct a; destruct a0; destruct b; destruct c; simpl in *.
    apply (fmor_preserves_comp (x⋊-)); auto.
    Defined.

  Instance PreMonoidalFullSubcategory_is_Binoidal : BinoidalCat S PreMonoidalFullSubcategory_bobj :=
    { bin_first := PreMonoidalFullSubcategory_first
    ; bin_second := PreMonoidalFullSubcategory_second }.

  Definition PreMonoidalFullSubcategory_assoc
    : forall a b,
      (PreMonoidalFullSubcategory_second a >>>> PreMonoidalFullSubcategory_first b) <~~~>
      (PreMonoidalFullSubcategory_first  b >>>> PreMonoidalFullSubcategory_second a).
    Defined.

  Definition PreMonoidalFullSubcategory_assoc_ll
    : forall a b,
      PreMonoidalFullSubcategory_second (a⊗b) <~~~>
      PreMonoidalFullSubcategory_second b >>>> PreMonoidalFullSubcategory_second a.
    intros.
    Defined.

  Definition PreMonoidalFullSubcategory_assoc_rr
    : forall a b,
      PreMonoidalFullSubcategory_first (a⊗b) <~~~>
      PreMonoidalFullSubcategory_first a >>>> PreMonoidalFullSubcategory_first b.
    intros.
    Defined.

  Definition PreMonoidalFullSubcategory_I := existT _ pmI Pobj_unit.

  Definition PreMonoidalFullSubcategory_cancelr
    : PreMonoidalFullSubcategory_first PreMonoidalFullSubcategory_I <~~~> functor_id _.
    Defined.

  Definition PreMonoidalFullSubcategory_cancell
    : PreMonoidalFullSubcategory_second PreMonoidalFullSubcategory_I <~~~> functor_id _.
    Defined.

  Instance PreMonoidalFullSubcategory_PreMonoidal
    : PreMonoidalCat PreMonoidalFullSubcategory_is_Binoidal PreMonoidalFullSubcategory_I :=
  { pmon_assoc           := PreMonoidalFullSubcategory_assoc 
  ; pmon_assoc_rr        := PreMonoidalFullSubcategory_assoc_rr
  ; pmon_assoc_ll        := PreMonoidalFullSubcategory_assoc_ll
  ; pmon_cancelr         := PreMonoidalFullSubcategory_cancelr
  ; pmon_cancell         := PreMonoidalFullSubcategory_cancell
  }.
  Defined.
End PreMonoidalFullSubcategory.
*)
