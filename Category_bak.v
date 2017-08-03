Require Export Coq.Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.
Require Import JMeq.
Require Import ProofIrrelevance.
Require Import Program.

Theorem excluded_middle (A : Prop) : A \/ ~A.
Proof. Admitted.

Theorem f_nequal_exists {A B : Type} (f g : A -> B) :
  f <> g -> exists x, f x <> g x.
Proof. Admitted.

Theorem f_img_dec {A B : Type} (f : A -> B) (b : B) : 
  {exists a, f a = b} + {forall a, f a <> b}.
Proof. Admitted.

Reserved Notation "f << g" (at level 12, right associativity).

Class Category : Type := {
  Ob : Type;
  Hom : Ob -> Ob -> Type;

  compose : forall {a b c : Ob} , Hom b c -> Hom a b -> Hom a c 
    where "f << g" := (compose f g);
  
  assoc : forall {a b c d : Ob} (f : Hom c d) (g : Hom b c) (h : Hom a b),
    f << g << h = (f << g) << h;

  id : forall {a : Ob}, Hom a a;

  id_unit_l : forall {a b : Ob} (f : Hom a b), id << f = f;
  id_unit_r : forall {a b : Ob} (f : Hom a b), f << id = f;
}.

Notation "f << g" := (compose f g).

Program Definition SetCat : Category := {|
  Ob := Set;
  Hom := fun A B => A -> B;
  compose := fun A B C (f : B -> C) (g : A -> B) => fun x => f (g x);
  (*eqv := fun A B (f : A -> B) (f' : A -> B) =>
        forall (x : A), f x = f' x;*)
|}.

Definition Injective {A B : Set} (f : A -> B) :=
  forall (a b : A), a <> b -> f a <> f b.

Lemma injective_equals {A B : Set} (f : A -> B) (H : Injective f) : 
  forall (x y : A), f x = f y -> x = y.
Proof. 
  intros. unfold Injective, not in *. 
  destruct (excluded_middle (x = y)).
  - assumption.
  - unfold not in *. contradiction (H _ _ H1 H0).
Qed.

Definition Mono {C : Category} {a b : Ob} (f : Hom a b) :=
  forall (c : Ob) (g h : Hom c a), g <> h -> f << g <> f << h.

Lemma const_eq {A B : Type} (x y : B) :
  A -> (fun (_:A) => x) = (fun (_:A) => y) -> x = y.
Proof. intros z H. apply (equal_f H z). Qed.

Theorem mono_iff_injective {A B : Set} (f : A -> B) :
  Injective f <-> Mono (C := SetCat) f.
Proof.
  split. 
  - unfold Injective, Mono. intros.
    destruct (f_nequal_exists g h H0).
    unfold not in *. intros.
    apply (H (g x) (h x) H1).
    apply (equal_f H2).
  - unfold Mono, Injective. intros.
    unfold not in *. intros.
    apply (H unit (fun _ => a) (fun _ => b)).
    + intros. apply H0. apply (const_eq a b tt H2).
    + unfold "<<". simpl. apply functional_extensionality.
      intros. assumption.
Qed.

Definition Surjective {A B : Type} (f : A -> B) :=
  forall (b : B), exists (a : A), f a = b.

Definition Epi {C : Category} {a b : Ob} (f : Hom a b) :=
  forall (x : Ob) (g h : Hom b x), g << f = h << f -> g = h.

Theorem epi_iff_surjective {A B : Set} (f : A -> B) :
  Surjective f <-> Epi (C := SetCat) f.
Proof.
  split.
  (* Surjective f -> Epi f *)
  (* Assume H: forall b : B, exists a : A, f a = b because Surjective f*)
  (* Assume H0: g << f = h << f *)
  (* Goal: Prove g = h *)
  (* Let b : B.
     Then there exists an a : A such that f a = b.
     Since H0, we have that g (f a) = h (f a).
     Since f a = b, we have that g b = h b and we're done!
  *)
  - unfold Surjective, Epi. intros.
    pose proof (equal_f H0). unfold "<<" in *. simpl in *.
    clear H0. extensionality b.
    intros. destruct (H b) as [a].
    pose proof (H1 a).
    rewrite <- H0. assumption.
  (* Epi f -> Surjective f *)
  (* Assume H: forall (x : Ob) (g h : Hom B x), g << f = h << f -> g = h *)
  (* Assume b : B *)
  (* Goal: Prove exists a : A, f a = b i.e. b is in img(f) *)
  (* Let g1 = fun _ => true
     Let g2 = fun (b':B) => if b' : img(f) then true else false
     Then, by H with x = bool, we have that g1 = g2 if we can prove
     that g1 << f = g2 << f.
     By extensionality, assume an a : A and prove that
       g1 (f a) = g2 (f a) <->
       true = if (f a) : img f then true else false
     Since (f a) is trivially in the image of f, then true = true and
     g1 = g2.
     Since g2 was only true when b : img(f) and g1 = g2, and g1 is
     always true, we have shown that b is in the image of f.
  *)
  - unfold Epi, Surjective. intros.
    remember (fun (_:B) => true) as g1.
    remember (fun (b':B) => if (f_img_dec f b') then true else false) as g2.
    pose proof (H bool g1 g2).
    assert (g1 = g2).
    + apply H0. extensionality a. subst. simpl.
      destruct (f_img_dec f (f a)); [reflexivity |].
      contradiction (n a eq_refl).
    + subst. simpl in *. 
      pose proof (equal_f H1). simpl in H2.
      specialize (H2 b). destruct (f_img_dec f b);
          [assumption | inversion H2].
Qed.
      
Inductive Iso {C : Category} {a b : Ob} : Hom a b -> Type :=
  MkIso : forall (f : Hom a b) (g : Hom b a), 
             g << f = id /\ f << g = id -> Iso f.

Definition iso_inv {C : Category} {a b : Ob} {f : Hom a b} 
                  (i : Iso f) : Hom b a := 
  match i with
  | MkIso f g _ => g
  end.

Reserved Notation "a <+> b" (at level 20, right associativity).

Class Monoid (A : Type) : Type := {
  mempty : A;
  mappend : A -> A -> A where "a <+> b" := (mappend a b);

  mappend_assoc : forall (a b c : A), a <+> b <+> c = (a <+> b) <+> c;
  mempty_unit_l : forall (a : A), mempty <+> a = a;
  mempty_unit_r : forall (a : A), a <+> mempty = a;
}.

Notation "a <+> b" := (mappend a b).

Program Instance MonoidCat {A : Type} (m : Monoid A) : Category := {
  Ob := Type;
  Hom := fun _ _ => A;
  compose := fun a b c f g => f <+> g;
  (*eqv := fun _ _ (f : A) (f' : A) => f = f';*)
}.
Next Obligation. apply mappend_assoc. Defined.
Next Obligation. apply mempty. Defined.
Next Obligation. apply mempty_unit_l. Defined.
Next Obligation. apply mempty_unit_r. Defined.

(* Not sure if the category of monoids only has monoid with the same
   underlying set or what? How to represent them then?
   Objects aren't forall A, Monoid A, because those are free monoids...
   Maybe they're exists A, Monoid A?
*)
(*Definition MonHom {A B : Type} {ma : Monoid A} {mb : Monoid B} (f : A -> B)
          : Type :=
  forall (x y : A), f x <+> f y = f (x <+> y).

Program Instance MonoidsCat : Category := {
  Ob := forall (A : Type), Monoid A;
  Hom := fun ma mb => forall (A B : Type) (f : A -> B), @MonHom A B (ma A) (mb B) f;
}.
 

(*
  Let C be a category, and let f : a → b in C be iso
  with inverse g : b → a .
  Show that g is unique, i.e. for any g' 
  that is an inverse of f we have g' = g.
*)
Next Obligation.
  Set Printing All.
  unfold MonHom in *. intros.
  pose proof (X A B f x y).*)

(* Assume f : a -> b *)
(* Assume g : b -> a *)
(* Assume H : g << f   = id
          H0 : g' << f = id
          H1 : f << g  = id
          H2 : f << g' = id
*)
(* Goal: Prove g = g' *)
(* By transitivity, we have that g << f = g' << f.
   This means that H3 : forall (x : a), g (f x) = g' (f x).
   By functional extensionality, to prove g = g', we have to prove
   forall (y : b), g y = g' y.
   By H3, we get g (f (g' y)) = g' (f (g y)).
   By H1 and H2 we get g y = g' y, and our goal is proven.
*)
Example ex_1_1 (a b : Set) (f : a -> b) :
  forall (i : Iso (C := SetCat) f) (i' : Iso (C := SetCat) f), iso_inv i = iso_inv i'.
Proof.
  intros. destruct i as [f g H], i' as [f' g' H'].
  destruct H as [H1 H2], H' as [H1' H2']. unfold Hom in *. simpl in *.
  unfold SetCat_obligation_2 in *.
  pose proof (equal_f H1) as Heqf.
  extensionality x.
  specialize (Heqf (g' x)). simpl in Heqf.
  pose proof (equal_f H2') as Hid. simpl in Hid.
  rewrite (Hid x) in Heqf. apply Heqf.
Qed.

Lemma comp_pre {C : Category} {A B X : Ob} {f g : Hom A B} :
  f = g -> forall (h : Hom X A), f << h = g << h.
Proof.
  intros. unfold "<<". destruct C. subst.
  reflexivity.
Qed.

Lemma comp_post {C : Category} {A B X : Ob} (f g : Hom A B) :
  f = g -> forall (h : Hom B X), h << f = h << g.
Proof.
  intros. unfold "<<". destruct C. subst.
  reflexivity.
Qed.

(* Let C be a category, and let f : a → b in C be iso with inverse
   g : b → a.
   Show that g is unique, i.e. for any g' that is an inverse of 
   f we have g' = g.
 *)
(* Assume f : a -> b *)
(* Assume g : b -> a *)
(* Assume H : g << f   = id
          H0 : g' << f = id
          H1 : f << g  = id
          H2 : f << g' = id
*)
(* Goal: Prove g = g' *)
(* By componentitivity, we have that g << f = g' << f.
   We can pre-compose g to both sides to get g << f << g = g' << f << g.
   We can then use H1 to get g << id = g' << id and the
   id_unit_r to get g = g' and we're done!
*)
Example ex_1_1' (C : Category) (a b : Ob) (f : Hom a b) (g : Hom b a) :
  Iso f g -> forall g', Iso f g' -> g = g'.
Proof.
  unfold Iso. intros.
  destruct H, H0.
  pose proof H as H'.
  rewrite <- H0 in H'.
  pose proof (comp_pre H' g).
  rewrite <- !assoc in H3.
  rewrite H1 in H3.
  rewrite !id_unit_r in H3.
  apply H3.
Qed.

Class Functor (C : Category) (D : Category) : Type := {
  fob  : @Ob C -> @Ob D;
  farr : forall {a b : @Ob C}, @Hom C a b -> @Hom D (fob a) (fob b);
  farr_id : forall {a : @Ob C}, farr (b:=a) id = id;
  farr_dist : forall {a b c : @Ob C} {f : Hom a b} {g : Hom b c},
                farr (g << f) = farr g << farr f;
}.

Notation "C ->> D" := (Functor C D) (at level 14, right associativity).

Definition IdFunctor (C : Category) : C ->> C := {|
  fob := fun x => x;
  farr := fun a b arr => arr;
  farr_id := fun a => eq_refl;
  farr_dist := fun a b c f g => eq_refl;
|}.

Program Definition ConstantFunctor (C : Category) (D : Category)
    (d : @Ob D) : C ->> D := {|
  fob := fun c => d;
  farr := fun a b arr => id;
|}.

Next Obligation. rewrite id_unit_l. reflexivity. Defined.

(* Let F : C → D , and let f : a → b be an isomorphism in C .
   Show that F f : F a → F b is an isomorphism in D.
*)
(*
  Goal : Iso (farr f) (farr g)
  Assume H : Iso f g
  To prove Iso (farr f) (farr g), show that
         farr f << farr g = id
      /\  farr g << farr f = id
  The first part of the conjunction can be proven by
  farr_dist, yielding farr (f << g) = id, then by Iso f g
  we get farr id = id, and by farr_id we have id = id.
  The second part of the conjunction is proven by a similar argument.
*)
Example ex_1_2 (C D : Category) (a b : @Ob C) (F : C ->> D)
               (f : Hom a b) (g : Hom b a)
               : Iso f g -> Iso (farr f) (farr g).
Proof.
  intros. destruct H. unfold Iso in *. split.
  - rewrite <- farr_dist.
    rewrite H. apply farr_id.
  - rewrite <- farr_dist.
    rewrite H0. apply farr_id.
Qed.

(* Let F : C -> D, G : D -> E be functors, define G << F : C -> E and
   show that it is a functor.
*)

Program Definition fcompose {C D E : Category} (F : D ->> E) (G : C ->> D)
  : C ->> E := {|
  fob := fun a => fob (fob a);
  farr := fun a b arr => farr (farr arr);
|}.

Next Obligation. rewrite !farr_id. reflexivity. Defined.
Next Obligation. rewrite !farr_dist. reflexivity. Defined. 

Notation "F <<< G" := (fcompose F G) (at level 12, right associativity).

Definition NaturalitySquare {C D : Category} {F G : C ->> D} 
    (component : forall (a : @Ob C), Hom (@fob C D F a) (@fob C D G a))
    := forall {a b : @Ob C} (f : Hom a b),
         farr f << component a = component b << farr f.

Record NatTrans {C D : Category} (F G : C ->> D) := {
  component: forall (a : @Ob C), Hom (@fob C D F a) (@fob C D G a);
  nat_square : NaturalitySquare component; 
    (*@farr C D G a b f << component a = component b << @farr C D F a b f;*)
}.

Notation "F =>> G" := (NatTrans F G) (at level 13, right associativity).

Program Definition ncompose {C D : Category} {F G H : C ->> D}
    (u : G =>> H) (v : F =>> G) : F =>> H := {|
   component := fun a => @component C D G H u a << @component C D F G v a;
|}.

Program Definition IdNatTrans {C D : Category} (F : C ->> D) : F =>> F := {|
  component := fun a => id;
|}.

Next Obligation.
  unfold NaturalitySquare. intros.
  rewrite id_unit_l, id_unit_r.
  reflexivity.
Defined.

(* Assume C, D : Category
   Assume F, G, H : C ->> D (functors from C to D)
   Assume u : G =>> V
   Assume v : F =>> G
   Assume a, b : Ob C (objects in C)
   Goal : F f << u_a << v_a = u_b << v_b << F f
   That is, the diagram
   F a --v_a-> G a --u_a-> H a 
    |                       |
   F f                     F f
    |                       |
    v                       v
   F b --v_b-> G b --u_b-> H b
   commutes.                          
   By nat_square from u, we have that H1: F f << u_a = u_b << F f
   By nat_square from v, we have that H2: v_b << F f = F f << v_a
   Replacing left-to-right in the goal, we get first
   u_b << F f << v_a = u_b << v_b << F f  and then
   u_b << F f << v_a = u_b << F f << v_a  and we're done!
*)
Next Obligation. 
  unfold NaturalitySquare. intros.
  rewrite assoc.
  rewrite nat_square.
  rewrite <- !assoc.
  rewrite <- nat_square.
  reflexivity.
Defined.

(*Definition componentport {A : Type} {a b : A} (B : A -> Type) : a = b -> B a -> B b.
Proof.
  intros [] ?; assumption.
Defined.*)

(*
  https://homes.cs.washington.edu/~jrw12/dep-destruct.html
  Whew! This is not easy, as to use f_equal we cannot have a dependent
  record. So to unify the types we can do dependent destruction
  (from Program) and proof_irrelevance to discard the requirement
  that the proofs of nat_square are equal (since we don't care).
*)
Lemma NatTrans_equal {C D : Category} {F G : C ->> D}
    (u v : F =>> G) (p : component F G u = component F G v) :
    u = v.
Proof. dependent destruction u. dependent destruction v.
  simpl in p. dependent destruction p.
  f_equal. apply proof_irrelevance.
Qed.

Instance FunctorsCat (C D : Category) : Category := {
  Ob := C ->> D;
  Hom := fun F G => F =>> G;
  compose := fun a b c u v => ncompose u v;
}.
- intros. unfold ncompose. apply NatTrans_equal.
  simpl. extensionality x. rewrite assoc. reflexivity.
- intros. apply IdNatTrans.
- intros. simpl. apply NatTrans_equal. 
  extensionality x. simpl. rewrite id_unit_l. reflexivity.
- intros. simpl. apply NatTrans_equal.
  extensionality x. simpl. rewrite id_unit_r. reflexivity.
Defined.
(*
  Let F,G : C -> D be functors, and let µ : F => G. Show that µ is
  an isomorphism (in the category of functors between C and D) 
  if and only if its components are isomorphisms (in D) for all a ∈ C.
  Goal: Iso 
*)
Example ex_1_5 (Fun C D : Category) (H : Fun = FunctorsCat C D) 
               (F G : @Ob Fun) (F' G' : C ->> D)
               (pf : JMeq F F') (pg : JMeq G G')
               (u : Hom F G) (v : Hom G F)
               (u' : F' =>> G') (v' : G' =>> F') :
  Iso u v <-> forall (x : @Ob C), Iso (component F' G' u' x) (component G' F' v' x).
Proof.
  split.
  - intros. unfold Iso. split.
    + unfold Iso in *. destruct H0. unfold component.
      destruct v', u'. unfold NaturalitySquare in *.
    + Set Printing Implicit. subst. Set Printing Implicit.
      inversion pg. inversion pf. subst. unfold Hom, Iso in *.
      destruct H0. simpl in *.
      unfold ncompose, IdNatTrans in *. simpl in *.
      inversion H0. inversion H2.
      Set Printing Implicit.
      unfold Hom in *. unfold component in *. simpl in *.
      unfold "<<" in *. dependent destruction D. simpl in *.
      dependent destruction v'.
      dependent destruction u'.
      dependent destruction v.
      dependent destruction u.
      dependent destruction F'.
      dependent destruction G'.
      simpl in *. unfold Ob, Hom in *.
      dependent destruction C. simpl in *.
      extensionality y.
      












