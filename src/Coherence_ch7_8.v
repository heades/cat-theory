Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.
Require Import ProductCategories_ch1_6_1.
Require Import NaturalTransformations_ch7_4.

(* these are the coherence diagrams found in Definition 7.23 of Awodey's book *)

(* DO NOT try to inline this into [Pre]MonoidalCat; it triggers a Coq resource consumption bug *)

Section Coherence.
  Context `{C:Category}
           {bobj:C->C->C}
           (first  : forall a b c:C, (a~~{C}~~>b) -> ((bobj a c)~~{C}~~>(bobj b c)))
           (second : forall a b c:C, (a~~{C}~~>b) -> ((bobj c a)~~{C}~~>(bobj c b)))
           (assoc  : forall a b c:C, (bobj (bobj a b) c) ~~{C}~~> (bobj a (bobj b c))).

  Record Pentagon :=
  { pentagon :   forall a b c d,    (first _ _ d (assoc a b c ))  >>>
                                                 (assoc a _ d )   >>>
                                   (second _ _ a (assoc b c d )) 
                                              ~~ (assoc _ c d )   >>>
                                                 (assoc a b _ )
  }.

  Context {I:C}
          (cancell : forall a    :C,              (bobj I a) ~~{C}~~> a)
          (cancelr : forall a    :C,              (bobj a I) ~~{C}~~> a).

  Record Triangle :=
  { triangle :  forall a b, (first _ _ b (cancelr a)) ~~ (assoc a I b) >>> (second _ _ a (cancell b))

  (* 
   * This is taken as an axiom in Mac Lane, Categories for the Working
   * Mathematician, p163, display (8), as well as in Awodey (second
   * triangle diagram).  However, it was shown to be eliminable by
   * Kelly in Theorem 6 of
   * http://dx.doi.org/10.1016/0021-8693(64)90018-3 but that was under
   * different assumptions.  To be safe we include it here as an
   * axiom.
   *)
  ; coincide :  (cancell I) ~~ (cancelr I)
  }.

End Coherence.

Coercion pentagon : Pentagon >-> Funclass.
Coercion triangle : Triangle >-> Funclass.

Implicit Arguments pentagon [ Ob Hom C bobj first second assoc ].
Implicit Arguments triangle [ Ob Hom C bobj first second assoc I cancell cancelr ].
Implicit Arguments coincide [ Ob Hom C bobj first second assoc I cancell cancelr ].
