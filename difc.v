Require Import FSets.FMapList FSets.FMapFacts FSets.FSetInterface Arith ZArith.
Require Import Structures.OrderedTypeEx FSets.FSetList.

(** * Decentralised Information Flow Control

    This library provides tools for reasoning about decentralised
    information flow control (DIFC). This was originally introduced
    by #<a href="https://www.cs.cornell.edu/andru/papers/iflow-sosp97">Myers et al.</a># . *)

Module ReaderMap := FMapList.Make(Nat_as_OT).
Module ReaderSet := FSetList.Make(Nat_as_OT).
Module SetFacts := FSetFacts.WFacts_fun(Nat_as_OT)(ReaderSet).
Module MapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(ReaderMap).
Module MapProps := FMapFacts.WProperties_fun(Nat_as_OT)(ReaderMap).

(** A label is usually represented as both a set of owners and a relation between each owner
    and their set of readers. For simplicity, we only track the later as the domain of that
    relation is identical to the set of owners. *)

Record label := {
  readers : ReaderMap.t ReaderSet.t;
}.

Definition label_equal (l1 l2 : label) : Prop :=
  forall (k : ReaderMap.key),
  match ReaderMap.find k l1.(readers), ReaderMap.find k l2.(readers) with
    | Some s, Some s' => s = s' /\ ReaderSet.Equal s s'
    | None, None => true = true
    | _, _ => false = true
  end.

(** The effective reader set of a label [l] is the set of readers that
    _all_ owners agree on sharing the data with. *)

Definition effective_reader (l : label) :=
    ReaderMap.fold (fun _ => ReaderSet.inter) l.(readers) ReaderSet.empty.

Definition is_an_owner (k : ReaderMap.key) (v : label) : Prop :=
    ReaderMap.mem k v.(readers) = true.

Definition is_some {X : Type} (v : option X) : bool :=
    match v with
    | Some _ => true
    | None => false
    end.

Lemma owner_implies_readers :
  forall (k : ReaderMap.key) (v : label),
  is_an_owner k v ->
  is_some (ReaderMap.find k v.(readers)) = true.
Proof.
    intros.
    unfold is_an_owner in H.
    destruct ReaderMap.find eqn:Hfind.
    - unfold is_some. reflexivity.
    - apply ReaderMap.mem_2 in H.
      apply MapFacts.not_find_in_iff in Hfind.
      unfold not in Hfind.
      contradiction.
Qed.

(** ** Restrictions

    Whenever we update labels, we're usually interested in ensuring that it is a
    _restriction_. A restriction relates two labels to each other, [l1] and [l2].

    Firstly, it says that the owners in [l1] are a subset of the owners in [l2].

    Secondly, it says that for all the owners in [l1], the readers of that owner
    is a superset of the readers described for the same owner in [l2].

    Together this prevents an information leak when relabelling from [l1] to [l2].
*)

Definition is_restriction (v : label) (v' : label) : Prop :=
    (* The owner set of the initial labeling  *)
    (forall owner, is_an_owner owner v -> is_an_owner owner v') /\
    (* For every owner, the set of their readers is a subset of the initial readers
       in the relabelling. *)
    (forall owner,
      is_an_owner owner v ->
      let readers' := ReaderMap.find owner v'.(readers) in
      let readers := ReaderMap.find owner v.(readers) in
      match readers', readers with
      | Some r', Some r =>
        (forall reader, ReaderSet.mem reader r = true -> ReaderSet.mem reader r' = true)
      | _, _ => ~(is_an_owner owner v')
      end
    ).

Search f_equal.

Lemma some_not_none_exists : forall (k : ReaderMap.key) (v : label),
  (exists e, ReaderMap.find k (readers v) = Some e) ->
  ReaderMap.find k (readers v) <> None.
Proof.
  intros.
  destruct H.
  rewrite H.
  discriminate.
Qed.

Lemma some_not_none : forall (k : ReaderMap.key) (v : label) (e : ReaderSet.t),
  ReaderMap.find k (readers v) = Some e ->
  ReaderMap.find k (readers v) <> None.
Proof.
  intros.
  rewrite H.
  unfold not.
  discriminate.
Qed.

Lemma mem_find_iff : forall (k : ReaderMap.key) (v : label),
  ReaderMap.mem k (readers v) = true <->
  exists e, ReaderMap.find k (readers v) = Some e.
Proof.
  split.
  - intros Hmem.
    apply ReaderMap.mem_2 in Hmem.
    destruct (ReaderMap.find k (readers v)) eqn:Hfind.
    * exists t.
      auto.
    * apply MapFacts.not_find_mapsto_iff in Hfind.
      contradiction.
  - intros Hfind_exist.
    apply some_not_none_exists in Hfind_exist.
    apply MapFacts.in_find_iff in Hfind_exist.
    apply ReaderMap.mem_1.
    assumption.
Qed.

Lemma all_find_is_all_in (l : label) (l' : label):
  forall (k : ReaderMap.key),
  ReaderMap.find k (readers l) = ReaderMap.find k (readers l')
  ->
  ReaderMap.mem k (readers l) = ReaderMap.mem k (readers l').
Proof.
    intros.
    destruct (ReaderMap.find (elt:=ReaderSet.t) k (readers l)) eqn:Hfind.
    - apply some_not_none in Hfind.
      apply MapFacts.in_find_iff in Hfind.
      apply ReaderMap.mem_1 in Hfind.
      symmetry in H.
      apply some_not_none in H.
      apply MapFacts.in_find_iff in H.
      apply ReaderMap.mem_1 in H.
      rewrite Hfind.
      rewrite H.
      reflexivity.
    - apply MapFacts.not_find_in_iff in Hfind.
      apply MapFacts.not_mem_in_iff in Hfind.
      symmetry in H.
      apply MapFacts.not_find_in_iff in H.
      apply MapFacts.not_mem_in_iff in H.
      rewrite Hfind.
      rewrite H.
      reflexivity.
Qed.

(** Our first theorem is that if two labels are equal then that is a restriction. *)

Theorem equal_labels_are_a_restriction :
    forall (l : label) (l' : label),
    label_equal l l' -> is_restriction l l'.
Proof.
    intros l l' eq.
    unfold is_restriction.
    split.
    - unfold is_an_owner.
      unfold label_equal in eq.
      intros some_owner H.
      apply mem_find_iff in H.
      destruct H.
      specialize (eq some_owner).
      rewrite H in eq.
      apply mem_find_iff.
      destruct (ReaderMap.find (elt:=ReaderSet.t) some_owner (readers l')) eqn:HF.
       + exists x.
         f_equal. symmetry.
         destruct eq.
         assumption.
       + discriminate eq.
   - intros.
     unfold label_equal in eq.
     unfold is_an_owner in H.
     apply mem_find_iff in H.
     destruct (ReaderMap.find (elt:=ReaderSet.t) owner (readers l')) eqn:H'.
        + destruct (ReaderMap.find (elt:=ReaderSet.t) owner (readers l)) eqn:H''.
            * intros.
              specialize (eq owner).
              rewrite H'' in eq.
              rewrite H' in eq.
              destruct eq.
              unfold ReaderSet.Equal in H2.
              apply ReaderSet.mem_2 in H0.
              specialize (H2 reader).
              apply ReaderSet.mem_1.
              apply H2.
              assumption.
            * destruct H.
              discriminate H.
        + unfold is_an_owner.
          apply MapFacts.not_find_in_iff in H'.
          unfold not in H'.
          unfold not.
          intros.
          apply ReaderMap.mem_2 in H0.
          contradiction.
Qed.

(** ** Least Restrictive Label

    It is often the case that we need to combine labels. If we have two inputs
    that are combined into an output, then the output is the result of _joining_
    the labels of the inputs.
*)

Definition join (l : label) (l' : label) : label :=
  let folder (k : ReaderMap.key) (elt : ReaderSet.t) (acc : ReaderMap.t ReaderSet.t) : ReaderMap.t ReaderSet.t :=
    match ReaderMap.find k (readers l') with
    | Some s' => ReaderMap.add k (ReaderSet.inter elt s') acc
    | None => ReaderMap.add k elt acc
    end
  in
  let r := ReaderMap.fold folder (readers l) (ReaderMap.empty ReaderSet.t) in
  {| readers := r |}.

Lemma mem_implies_not_empty :
  forall (l : label),
  (exists k, ReaderMap.mem k (readers l) = true) ->
  ((readers l) <> ReaderMap.empty ReaderSet.t).
Proof.
    intros.
    destruct H.
    unfold not.
    intros.
    rewrite H0 in H.
    specialize (MapFacts.empty_in_iff ReaderSet.t x).
    intros.
    apply H1.
    apply ReaderMap.mem_2 in H.
    assumption.
Qed.

Lemma join_readers_subset :
    forall (k : ReaderMap.key) (l : label) (l' : label),
    ReaderMap.mem k (readers l) = true ->
    ReaderMap.mem k (readers (join l l')) = true.
Proof.
    intros.
    apply ReaderMap.mem_1.
    unfold join.
    simpl.
    apply MapProps.fold_rec.
        - intros.
          apply MapFacts.empty_in_iff.
          specialize (mem_implies_not_empty l).
          intros.
          apply H1.
          + exists k. assumption.
          + contradiction H1.




Lemma mem_subset_iff (k : ReaderMap.key) (l : label) (l' : label) :
    ReaderMap.mem k (readers l) = true /\
    (forall k', ReaderMap.mem k' (readers l) = true /\ ReaderMap.mem k' (readers l') = true)
    -> ReaderMap.mem k (readers l') = true.
Proof.
    intros.
    destruct H.
    specialize (H0 k).
    destruct H0.
    assumption.
Qed.

(** And joining labels is a restriction *)

Theorem joining_is_a_restriction :
  forall (l : label) (l' : label),
  is_restriction l (join l l').
Proof.
    intros.
    unfold is_restriction.
    split.
    - unfold is_an_owner.
      intros.
      apply (mem_subset_iff owner l (join l l')) in H.



