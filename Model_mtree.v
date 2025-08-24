Require Import ZArith.

Local Open Scope Z_scope.
Section model.

(*
A hash is a function that has some nice cryptographic properties
(e.g. one-way, avalanche effect, etc. ). However, for our model,
we only care that the hash function is injective (that every element
in the domain maps to one element in the codomain.). For purposes of
modeling, we assume the probability of a hash collision is zero.
*)

(* Use numbers for model *)
Definition hash_func := Z -> Z.

Locate Z.eq.
Locate eq.
Print eq.
Print Z.eq.
Search Z "eq" "dec".
Print Z.eq_dec.

Definition hash_func_injective (f: hash_func) := forall (x1 x2: Z),
((x1 = x2 -> False) -> (f x1 = f x2 -> False)) /\
((f x1 = f x2) -> (x1 = x2)).

Definition bad_hash_func (input: Z): Z :=
    0.

Example bad_hash_not_inj: hash_func_injective bad_hash_func -> False.
Proof.
    intros.
    unfold hash_func_injective in H.
    specialize H with 0 1.
    unfold bad_hash_func in H.
    apply H.
        - intros.
        discriminate.
        - reflexivity.
Qed. 
    
(* A merkle tree is a n-ary tree that contains a hash of:
    - the data it points to, if it is a child node.
    - the hashes of all the children, if it is an internal node.
*)
End model.
