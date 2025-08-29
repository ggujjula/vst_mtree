Require Import ZArith.
Require Import Coq.Program.Equality.

Local Open Scope Z_scope.
Section model.


(*
A hash is a function that has some nice cryptographic properties
(e.g. one-way, avalanche effect, etc. ). However, for our model,
we only care that the hash function is injective (that every element
in the domain maps to one element in the codomain.). For purposes of
modeling, we assume the probability of a hash collision is zero.
*)
Parameter data : Type.
Parameter data_nil: data.
Parameter hash : Type.
Parameter hash_func : data -> hash.
Parameter hash_to_data : hash -> data.
Axiom hash_func_inj : forall x y: data,
    hash_func x = hash_func y -> x = y.
Parameter data_eq_dec : forall x y: data, {x=y} + {x<>y}.
Parameter hash_eq_dec : forall x y: hash, {x=y} + {x<>y}.
Parameter data_combine : data -> data -> data.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* A merkle tree is a n-ary tree that contains a hash of:
    - the data it points to, if it is a child node.
    - the hashes of all the children, if it is an internal node.
*)
Inductive mtree :=
| Child (h: hash) (d: data)
| Internal (h: hash) (c: list mtree).

Definition hash_mtree (t: mtree) :=
match t with
| Child h _ => h
| Internal h _ => h
end.

(*
Definition test : list Z := [0 ; 2 ; 3].
*)

Search list "fold".
Inductive valid_mtree : forall mtree, Prop :=
| ValidChild : forall (h : hash)(d: data), hash_func d = h -> valid_mtree (Child h d)
| ValidInternal : forall (h: hash) (xs: list mtree),
    (xs <> nil) -> (h = hash_func (List.fold_left data_combine (List.map hash_to_data (List.map hash_mtree xs)) data_nil))
    -> (List.Forall valid_mtree xs)
    -> valid_mtree (Internal h xs)
.

(*
Definition trivial_mtree := Child [0] [0].
Check trivial_mtree.
Example trivial_mtree_valid : valid_mtree test_hash (trivial_mtree).
Proof.
    apply ValidChild.
    unfold test_hash.
    reflexivity.
Qed.

Definition trivial_mtree_bad := Child test_hash [0] [1 ; 2 ; 3].
Check trivial_mtree_bad.
Example trivial_mtree_valid_bad : ~ valid_mtree test_hash (trivial_mtree_bad).
Proof.
    unfold not.
    intros.
    inversion H.
    unfold test_hash in H2.
    discriminate.
Qed.
*)

Lemma valid_mtree_children : forall
    (t: mtree)
    (h: hash)
    (xs: list mtree),
valid_mtree t -> t = Internal h xs -> List.Forall valid_mtree xs.
Proof.
    intros.
    rewrite H0 in H.
    inversion H.
    exact H5.
Qed.

Lemma valid_mtree_subtree : forall
    (t: mtree)
    (h: hash)
    (xs: list mtree)
    (x: mtree),
valid_mtree t -> t = Internal h xs -> List.In x xs -> valid_mtree x.
Proof.
    intros.
    assert (List.Forall valid_mtree xs).
        - apply valid_mtree_children with t h; auto.
        - rewrite List.Forall_forall in H2.
        specialize (H2 x).
        apply H2.
        apply H1.
Qed.

Lemma mtree_data_child_inj : forall
    (t1 t2: mtree)
    (h1 h2: hash)
    (d1 d2: data),
    valid_mtree t1 ->
    valid_mtree t2 ->
    t1 = Child h1 d1 ->
    t2 = Child h2 d2 ->
    h1 = h2 ->
    d1 = d2.
Proof.
    intros.
    inversion H; subst.
    inversion H0; subst.
    injection H5.
        - intros.
        subst.
        apply hash_func_inj.
        apply H2.
        - discriminate. 
Qed.

Lemma mtree_data_internal_inj : forall
    (t1 t2: mtree)
    (h1 h2: hash)
    (xs1 xs2: list mtree),
    valid_mtree t1 ->
    valid_mtree t2 ->
    t1 = Internal h1 xs1 ->
    t2 = Internal h2 xs2 ->
    h1 = h2 ->
    xs1 = xs2.
Proof.
    intros.
    inversion H; subst.
        - discriminate.
        - inversion H0; subst.
        injection H7.
        intros.
        rewrite H1 in H2.
        apply hash_func_inj in H2.
        (* In order to prove this, I have to be able to prove
        that if the combination of hashes is equal, then the
        hashes that make up the combo are equal.
        To do that I need to know that;
            - There is a canonical way to split up a data
            into a series of hashes.
            Ex: In reality, hashes are a fixed length of bytes.
            If I get a combination of hashes, I can split them
            by partitioning the data by the hash length.
        *)
Admitted.

(*
Check mtree_data_child_inj.
Lemma mtree_data_inj : forall
    (t1 t2: mtree),
    valid_mtree t1 ->
    valid_mtree t2 ->
    hash_mtree t1 = hash_mtree t2 ->
    (exists d1 d2: data, mtree_data_child_inj t1 t2 (hash_mtree t1) (hash_mtree t2) d1 d2)
    \/ mtree_data_internal_inj t1 t2.
Proof.
Admitted.
*)
    

End model.
