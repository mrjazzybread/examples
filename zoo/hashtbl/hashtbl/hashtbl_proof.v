Require Export hashtbl__types hashtbl__code.
From stdpp Require Import numbers list gmap.

From zoo Require Import
  prelude.

From zoo_std
  Require Import array option list bqueue.

From zoo.language Require Import
  typeclasses
  notations.

From zoo.diaframe Require Import
  diaframe.

From zoo Require Import options.

Require Import iris.algebra.dfrac.
From listz Require Import listz.
Notation len := length.

Section spec.

Context `{zoo_G : !ZooG Σ}.

Notation iProp := (iProp Σ).

(* For simplicity's sake, we assume that keys can be projected into
   the logical level. *)
Variable K : Type.
Parameter Key : K -> val.
(* Decidable equality over keys. *)
Global Declare Instance EqK : EqDecision K.
(* The type of keys is countably infinite. *)
Global Declare Instance CoutntK : Countable K.

Notation hmap := (gmap K (list val)).

Definition bucket := (list (K * val)).

Fixpoint bucket_to_val (b : bucket) : val :=
  match b with
  | nil => §Nil
  | cons v t =>
      let (k, v) := v in
      ‘Cons( Key k, v , (bucket_to_val t))
  end%V.

Fixpoint remove_assoc (k : K) (l : bucket) :=
  match l with
  |[] => []
  |(k', v) :: t =>
     if (decide (k = k'))
     then t
     else
       (k', v) :: remove_assoc k t
  end.

Axiom eq_spec :
  ∀ k1 k2,
  {{{ True }}}
    hashtbl٠eq (Key k1) (Key k2)
  {{{ b, RET #b; ⌜ b = true ↔ k1 = k2 ⌝ }}}.

Lemma remove_assoc_spec k _b b :
  _b = bucket_to_val b ->
  {{{ True }}}
    hashtbl٠remove_assoc (Key k) _b
    {{{ r v, RET (r, v);
        ⌜ r = true%V <-> (∃ v, (k, v) ∈ b) ⌝ ∗
        ⌜ bucket_to_val (remove_assoc k b) = v ⌝ }}}.
Proof.
  iInduction b as [|[k' v'] b] "IH" forall (_b);
    iIntros "%H %ϕ _ Hϕ"; wp_rec; simpl in *;
    subst _b; wp_pures.
  - iApply "Hϕ"; iModIntro; iSplit; iPureIntro; auto. split; intros H; try done.
    destruct H. by apply elem_of_nil in H.
  - wp_apply (eq_spec with "[//]") as "%e %E".
    destruct e; wp_pures.
    + destruct E as [E _]. iApply "Hϕ".
      rewrite E; auto. iPureIntro; split.
      { split; auto. intros. eexists.
        constructor. }
      { rewrite decide_True; auto. }
    + wp_apply "IH"; auto.
      iIntros "%r %v [%H1 %H2]".
      { assert (NE :k' ≠ k).
        { intros ?. subst. destruct E as [_ E].
          by discriminate E. }
        wp_pures. iApply "Hϕ". iModIntro.
        iSplit; iPureIntro.
        + split; intros.
          { apply H1 in H as [??].
            eexists. by constructor. }
          { rewrite H1. destruct H.
            eexists.
            rewrite elem_of_cons in H.
            destruct H as [H | H]; eauto.
            injection H. intros. by subst. }
        + rewrite decide_False; auto. simpl.
          by rewrite H2. }
Qed.

Parameter hash : K -> Z.

Axiom hash_nonneg : ∀ k, hash k >= 0.

Notation indexZ k len := (hash k mod len)%Z.

Notation filter_key k l :=
  (base.filter (fun (x: K * val) => let (k', _) := x in k' = k) l).

(* Lemmas for filtering association lists *)

Lemma filter_key_nin :
  forall k b,
    (∀ v : val, (k, v) ∉ b) ->
    filter_key k b = [].
Proof.
  intros k b H1.
  induction b as [|[k' v] t Ih].
  - auto.
  - rewrite filter_cons_False.
    + specialize H1 with v.
      rewrite not_elem_of_cons in H1.
      destruct H1.
      intros H3. by subst.
    + apply Ih. intros v'.
      specialize H1 with v'.
      rewrite not_elem_of_cons in H1.
      by destruct H1.
Qed.

Hint Rewrite
  @filter_nil
  @filter_cons_False
  @filter_cons_True
  using done : cfilter.

Ltac filter := autorewrite with cfilter.

Lemma filter_key_cons :
  forall k k' v b1 b2,
    filter_key k b1 = filter_key k b2 ->
    filter_key k ((k', v)::b1) = filter_key k ((k', v) :: b2).
Proof.
  intros.
  destruct (decide (k = k')).
  + subst. filter. by f_equal.
  + by filter.
Qed.

(* Association lists *)

(* [l' = remove_assoc_list k l] returns a list [l'] where the first
   binding of key [k] is removed.
   If no such binding exists then [l' = l]. *)
Fixpoint remove_assoc_list (k : K) (l : bucket) :=
  match l with
  |[] => []
  |(k', v) :: t =>
     if (decide (k = k'))
     then t
     else
       (k', v) :: remove_assoc_list k t
  end.

(* If a binding is in the result of [remove_assoc_list], then it was
in the original association list *)

Lemma remove_assoc_in :
  forall l k k' v,
    (k', v) ∈ remove_assoc_list k l ->
    (k', v) ∈ l.
Proof.
  intros l k k' v H1.
  induction l as [|[k'' v'] t Ih]; simpl in H1.
  + by apply not_elem_of_nil in H1.
  + destruct decide in H1; apply elem_of_cons; auto.
    apply elem_of_cons in H1 as [H1 | H1]; auto.
Qed.

(* The list of bindings for [k] in [remove_assoc_list l] is equal to
   [tl (filter_key k l)] *)

Lemma remove_assoc_bucket_eq :
  forall k b b',
    b' = remove_assoc_list k b ->
    filter_key k b' = tl (filter_key k b).
Proof.
  intros k b.
  induction b as [|[k' v] t Ih]; simpl; intros b' H1; subst b'. auto.
  case_decide.
  - subst. by filter.
  - filter. auto.
Qed.

(* The list of bindings for [k'] in [remove_assoc_list k b] is equal
   to the list of bindings for [k'] in [l], provided that [k' ≠ k].*)

Lemma remove_assoc_bucket_ne :
  forall k k' b b',
    b' = remove_assoc_list k b ->
    k' ≠ k ->
    filter_key k' b' = filter_key k' b.
Proof.
  intros k k' b.
  induction b as [|[k'' v] t Ih]; simpl; intros b' H1 H2; subst b'; auto.
  case_decide.
  - subst. by filter.
  - apply filter_key_cons. by apply Ih.
Qed.

Axiom hashtbl٠hash_spec : ∀ k,
  {{{ True }}}
    hashtbl٠hash (Key k)
  {{{ r, RET #r; ⌜ r = hash k ⌝ }}}.

Lemma hashtbl٠index_spec k n:
  {{{ True }}}
    hashtbl٠index (Key k) #n
  {{{ r, RET #r; ⌜ r = indexZ k n ⌝ }}}.
Proof.
  iIntros "%ϕ _ Hϕ".
  wp_rec. wp_pures.
  wp_apply (hashtbl٠hash_spec with "[//]").
  iIntros. wp_pures.
  iApply "Hϕ". iPureIntro.
Admitted.

Lemma indexZ_range :
  ∀ A k (l : list A), length l > 0 -> valid (indexZ k (length l)) l.
Proof.
  intros.
  pose (hash_nonneg k).
  lia.
Qed.

(* Relates a list of buckets to a finite map of keys to lists of
   values, where [n] is the length of the [tbl].  For every key [k],
   [m !!! k] returns the list of values mapped to [k] in [tbl].
   If [k] is not in [tbl], [m !!! k] returns the empty list. *)
Definition valid_buckets (n : Z) (tbl : list bucket) (m : hmap) : Prop :=
  forall i b k,
    indexZ k n = i ->
    b = filter_key k (tbl !!! i) ->
    m !!! k = map snd b.

(* If a key [k] is in a bucket of index [i], then [i] must correspond
   to the hash of [k]. *)
Definition no_garbage (n : Z) (tbl : list bucket) : Prop :=
  forall i k v,
    listz.valid i tbl ->
    (k, v) ∈ (tbl !!! i) ->
    indexZ k n = i.

Locate zoo.common.list.

Lemma lookup_total_empty_list (m : hmap) k :
    m !! k = None ->
    m !!! k = [].
Proof.
  intros H. rewrite lookup_total_alt.
  by rewrite H.
Qed.

Lemma lookup_total_non_empty_list :
  forall (m : hmap) k x t,
    m !!! k = x :: t ->
    m !! k = Some(x :: t).
Proof.
  intros m k x t H.
  rewrite lookup_total_alt in H.
  destruct (m !! k); simpl in *; f_equal; done.
Qed.

Lemma lookup_total_Some :
  ∀ (m : hmap) k,
    m !! k ≠ None →
    m !! k = Some (m !!! k).
Proof.
  intros.
  remember (m !! k) as l.
  destruct l as [l|]. 2: done.
  by erewrite lookup_total_correct.
Qed.

Hint Rewrite
  lookup_total_Some
  lookup_total_empty_list
  using done : cmap.

Hint Rewrite
  (fin_maps.lookup_total_insert_ne (M:=gmap K) (A:=list val))
  (fin_maps.lookup_total_insert_eq (M:=gmap K) (A:=list val))
  using done : cmap.

Ltac hmap := autorewrite with cmap.

Tactic Notation "hmap" "in" hyp(h) :=
  autorewrite with cmap in h.

Tactic Notation "hmap" "in" "*" :=
  autorewrite with cmap in *.

Definition _add (m : hmap) (k : K) (v : val) := <[k:= v :: m !!! k]> m.

Lemma add_lookup_eq :
  forall m k v, _add m k v !!! k = v :: m !!! k.
Proof.
  intros.
  unfold _add.
  by hmap.
Qed.

Lemma add_lookup_neq :
  forall m k k' v,
    k ≠ k' →
    _add m k v !!! k' = m !!! k'.
Proof.
  intros.
  unfold _add.
  by hmap.
Qed.

Definition rm (m : hmap) (k : K) :=
  <[k:=tl (m !!! k)]> m.

Definition rm_add (m : hmap) (k : K) (v : val) :=
  _add (rm m k) k v.

Definition cardinality (h : hmap) :=
  (map_fold (fun _ (v : list val) acc => acc + len v) 0 h)%Z.

Lemma cardinality_empty :
  cardinality ∅ = 0%Z.
Proof.
  apply map_fold_empty.
Qed.

Lemma cardinality_insert_fresh :
  forall m k l n,
    cardinality m = n ->
    m !! k = None ->
    cardinality (<[k:=l]>m) = (len l + n)%Z.
Proof.
  intros.
  subst n.
  unfold cardinality.
  rewrite map_fold_insert; eauto with lia.
Qed.

Lemma cardinality_nonneg :
  ∀ m, cardinality m >= 0.
Proof.
  intros.
  induction m as [|k l] using map_first_key_ind.
  - by rewrite cardinality_empty.
  - erewrite cardinality_insert_fresh; eauto.
    pose (length_nonneg l). lia.
Qed.

Ltac tc := eauto with typeclass_instances lia.

Lemma cardinality_delete_present :
  forall m k l n,
    cardinality m = n ->
    m !! k = Some l ->
    (cardinality (delete k m) + len l)%Z = n.
Proof.
  intros. subst n. unfold cardinality.
  erewrite map_fold_delete with (m:=m); tc.
Qed.

Lemma cardinality_delete_present_alt :
  forall m k l n,
    cardinality m = n ->
    m !! k = Some l ->
    cardinality (delete k m) = (n - len l)%Z.
Proof.
  intros. subst. unfold cardinality.
  erewrite map_fold_delete with (m:=m) (R:=eq); tc.
  lia.
Qed.

Lemma cardinality_insert :
  forall m k l n,
    cardinality m = n ->
    cardinality (<[k:=l]>m) = (n + len l - len (m !!! k))%Z.
Proof.
  intros m k l n H1.
  destruct (decide (m !! k = None)).
  - hmap. erewrite cardinality_insert_fresh by auto.
    length. lia.
  - rewrite <- insert_delete_eq.
    erewrite cardinality_insert_fresh with (n:=(n - len (m !!! k))%Z). lia.
    + erewrite <- cardinality_delete_present_alt; auto with lia.
      by hmap.
    + by rewrite lookup_delete_eq.
Qed.

Lemma cardinality_delete :
  forall m n k,
    cardinality m = n ->
    cardinality (delete k m) = (n - len (m !!! k))%Z.
Proof.
  intros m n k H1.
  remember (m !! k) as l eqn:E.
  destruct l as [l|].
  + erewrite cardinality_delete_present_alt; eauto.
    rewrite <- E. f_equal. symmetry.
    by apply lookup_total_correct.
  + hmap. length. by rewrite delete_id.
Qed.

Ltac cinsert n := erewrite cardinality_insert by auto.

Lemma cardinality_empty_lists :
  forall m,
    (∀ k, m !!! k = []) →
    cardinality m = 0%Z.
Proof.
  intros m Hempty.
  induction m as [|k v m Hnone Hfirst Ih] using map_first_key_ind. by hmap.
  erewrite cardinality_insert.
  - hmap. list. specialize Hempty with k.
    rewrite fin_maps.lookup_total_insert_eq in Hempty.
    subst. by list.
  - apply Ih. intros k'.
    specialize Hempty with k'.
    rewrite fin_maps.lookup_total_insert in Hempty.
    case_decide; auto.
    subst. by hmap.
Qed.

Lemma cardinality_add :
  forall m n k v,
    cardinality m = n ->
    cardinality (_add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold _add.
  cinsert n.
  length. lia.
Qed.

Lemma cardinality_rm_empty :
  forall m n k,
    cardinality m = n ->
    m !!! k = [] ->
    cardinality (rm m k) = n%Z.
Proof.
  intros m n k H1 H2.
  unfold rm.
  cinsert n.
  rewrite H2. by length.
Qed.

Lemma cardinality_rm :
  forall m n k,
    cardinality m = n ->
    m !!! k ≠ [] ->
    cardinality (rm m k) = (n - 1)%Z.
Proof.
  intros.
  unfold rm.
  cinsert n.
  remember (m !!! k) as l eqn:E.
  destruct l. done.
  subst. by length.
Qed.

Lemma cardinality_rm_add_empty :
  forall m n k v,
    cardinality m = n ->
    m !!! k = [] ->
    cardinality (rm_add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold rm_add.
  erewrite cardinality_add by auto.
  erewrite cardinality_rm_empty by auto.
  lia.
Qed.

Lemma cardinality_rm_add :
  forall m n k v,
    cardinality m = n ->
    m !!! k ≠ [] ->
    cardinality (rm_add m k v) = n.
Proof.
  intros.
  unfold rm_add.
  erewrite cardinality_add by auto.
  erewrite cardinality_rm by auto. lia.
Qed.

Hint Rewrite
  cardinality_empty
  cardinality_add
  cardinality_rm
  cardinality_rm_empty
  cardinality_rm_add
  cardinality_rm_add_empty
  using done : card.

Implicit Types k : K.
Implicit Types v : val.

Lemma cardinality_extensionality :
  ∀ (m1 : hmap) m2,
    (∀ k, m1 !!! k = m2 !!! k) →
    cardinality m1 = cardinality m2.
Proof.
  induction m1 as [|k v m1 Hnone Hfirst Ih] using map_first_key_ind;
    intros m2 HLookup.
  - hmap. rewrite cardinality_empty.
    rewrite cardinality_empty_lists; auto.
    intros k. specialize HLookup with k.
    by rewrite lookup_total_empty in HLookup.
  - erewrite cardinality_insert by auto.
    hmap. erewrite Ih with (delete k m2).
    { erewrite cardinality_delete; auto.
      specialize HLookup with k. hmap in HLookup.
      subst v. by list. }
    { intros k'.
      destruct (decide (k = k')).
      - subst. rewrite fin_maps.lookup_total_delete_eq.
        by hmap.
      - rewrite fin_maps.lookup_total_delete_ne; auto.
       specialize HLookup with k'.
       by hmap in HLookup. }
Qed.

Implicit Types l : location.
Implicit Types _k _v : val.

Notation tbl_to_val tbl :=
  (fmap bucket_to_val tbl).

Definition HashtblArray (h : val) (m : hmap) : iProp :=
  ∃ (v : list val) tbl n, array_model h (DfracOwn 1) v ∗
           ⌜ v = tbl_to_val tbl ⌝ ∗
           ⌜ n = len tbl ⌝ ∗ ⌜0 < n⌝%Z ∗
           ⌜ no_garbage n tbl ⌝ ∗ ⌜ valid_buckets n tbl m ⌝.

Definition Hashtbl (h : val) (m : hmap) : iProp :=
  ∃ l arr,
    ⌜ h = #l ⌝ ∗ l.[buckets] ↦ arr ∗ HashtblArray arr m.

Lemma replicate_model (n : Z) :
  replicate n (§Nil)%V = tbl_to_val (replicate n []).
Proof.
  unfold tbl_to_val.
  by list.
Qed.

Lemma array٠make_spec sz v :
  {{{ ⌜0 ≤ sz⌝%Z }}}
    array٠make #sz v
  {{{ t, RET t; array_model t (DfracOwn 1) (replicate sz v) }}}.
Admitted.

(* Tactic stolen from marble :| *)
Ltac pack :=
  repeat match goal with
  | |- ∀ x, _ =>
      intro
  | |- _ ∧ _ =>
      split
  | |- ∃ x, _ =>
      eexists
  end.

Lemma create_spec (n : Z) :
    {{{ ⌜ 0 < n ⌝ }}}
      hashtbl٠create #n
    {{{ _h, RET _h; Hashtbl _h ∅}}}.
Proof.
  iIntros "%ϕ %S Hϕ".
  wp_rec. wp_apply+ array٠make_spec.
  { iPureIntro. lia. }
  iIntros "%t A".
  wp_block l.
  iApply "Hϕ".
  iUnfold Hashtbl;
  iExists l. do 2 iStep.
  unfold HashtblArray. iModIntro.
  iFrame. iExists _, _.
  repeat iSplit; iPureIntro; list; eauto.
  - by rewrite replicate_model.
  - by list.
  - unfold no_garbage. intros ???? H3.
      do 2 list in *.
      by apply not_elem_of_nil in H3.
  - intros ?**. do 2 list in *. by subst.
Qed.

Lemma no_garbage_insert :
  forall n k v i tbl b,
  len tbl = n ->
  no_garbage n tbl ->
  i = indexZ k n ->
  b = tbl !!! i ->
  no_garbage n (<[i:=(k, v) :: b]> tbl).
Proof.
  unfold no_garbage.
  intros n k v i tbl b H1 H2 H3 H4.
  intros i' k' v' H5 H6.
  list in H5.
  destruct (decide (i = i')).
  { subst i. list in H6.
    simpl in *.
    rewrite elem_of_cons in H6.
    destruct H6 as [H6 | H6].
    - injection H6. intros. by subst.
    - subst. eauto. }
  { list in H6. eauto. }
Qed.

Ltac case_bucket k n i :=
  destruct (decide (indexZ k n = i)).

Lemma valid_buckets_insert :
  forall i n tbl k v b m,
    n = len tbl ->
    0 < n ->
    i = indexZ k n ->
    b = tbl !!! i ->
    valid_buckets n tbl m ->
    valid_buckets n (<[i:=(k, v) :: b]> tbl)
      (_add m k v).
Proof.
  intros i n tbl k v b m ???? H5.
  intros i' b' k' ? ?.
  (* The updated map as described in the postcondition
     accurately models the updated hash table. *)
  unfold _add. destruct (decide (k = k')).
  + (* When we apply the updated map with the key we pass as
         argument. *)
    subst k'. hmap.
    subst. list. simpl. filter. simpl. f_equal.
    eauto with subst.
  + hmap. case_bucket k n i'; subst;
      list; simpl; filter; eauto.
Qed.

Lemma array٠set𑁒spec t (i : Z) vs v :
  {{{
        array_model t (DfracOwn 1) vs
  }}}
    array٠set t #i v
    {{{
          RET ();
          array_model t (DfracOwn 1) (<[i := v]> vs)
    }}}.
Proof.
Admitted.

Lemma array٠size𑁒spec t dq vs :
    {{{
      array_model t dq vs
    }}}
      array٠size t
    {{{
      RET #(len vs);
      array_model t dq vs
    }}}.
Proof.
Admitted.

Lemma array٠get𑁒spec t (i : Z) dq vs v :
    {{{
      array_model t dq vs ∗
      ( ⌜0 ≤ i < length vs⌝%Z -∗
        ⌜vs !! i = Some v⌝
      )
    }}}
      array٠get t #i
    {{{
      RET v;
      ⌜0 ≤ i < length vs⌝%Z ∗
      array_model t dq vs
    }}}.
Proof.
Admitted.

Lemma add'_spec h m k v :
     {{{ HashtblArray h m }}}
       hashtbl٠add' h (Key k) v
     {{{ RET (); HashtblArray h (_add m k v)}}}.
Proof.
  iIntros "%ϕ S Hϕ".
  wp_rec.
  iDestruct "S" as "(%l & %r & %n & H2 & (%H3 & %H4 & %H5 & %H6 & %H7))".
  wp_apply+ (array٠size𑁒spec with "H2").
  iIntros "H2".
  wp_pures.
  wp_apply+ (hashtbl٠index_spec with "[//]").
  iIntros.
  wp_pures. wp_apply+ (array٠get𑁒spec with "[H2]") as "[%H2 H3]".
  { iFrame. iPureIntro. intros. rewrite list_lookup_alt. split; auto. }
  wp_apply+ (array٠set𑁒spec with "H3") as "H3".
  iApply "Hϕ".
  iFrame.
  iExists (<[r0:=(k, v) :: r !!! r0]> r), _.
  assert (len r = len l).
  { rewrite H3. unfold tbl_to_val. by list. }
  repeat iSplit; iPureIntro; list; try done.
  - simpl. rewrite stdpp_buffer.expand_singleton.
    apply list_eq_same_length'_total.
    + unfold tbl_to_val. by list.
    + intros. rewrite list_lookup_total_fmap;
        list in *; try lia; simpl.
      destruct (decide (r0 = i)); list.
      { simpl. repeat f_equal. rewrite H3.
        by rewrite list_lookup_total_fmap; try lia. }
      { rewrite H3. by rewrite list_lookup_total_fmap; try lia. }
  - apply no_garbage_insert; eauto. subst. by list.
  - apply valid_buckets_insert; auto.
    subst. unfold tbl_to_val. by list.
Qed.

Definition FOLD {A}
  (permitted : list A -> Prop)
  (complete : list A -> Prop)
  (init : val)
  (body : val -> expr)
  (loop : val -> A -> expr)
  (S : iProp)
  :=
  ∀ inv,
    (∀ (x : A) (h1 : list A) (h2 : list A) (acc : val),
       {{{ inv h1 acc ∗ ⌜ h2 = h1 ++ [x] ⌝ ∗ ⌜ permitted h2 ⌝ }}}
       loop acc x
       {{{ acc', RET acc'; inv h2 acc' }}}) -∗
  {{{ inv [] init ∗ ⌜ permitted [] ⌝ ∗ S }}}
    body init
  {{{ r, RET r; ∃ h, inv h r ∗ ⌜ complete h ⌝ ∗ S }}}.

Definition ITER {A}
   (permitted : list A -> Prop)
   (complete : list A -> Prop)
   (body : expr)
   (loop : A -> expr)
   (S : iProp)
   :=
   FOLD permitted complete ()%V (λ _, body) (λ _, loop) S .

Parameter hashtbl٠iter : val.

Lemma bucket_iter_right_spec (_b : val) b (f : val) :
  ITER (λ h, h `prefix_of` reverse b)
    (λ h, h = reverse b)
    (hashtbl٠bucket_iter_right _b f)
    (λ (x : K * val), let (k, v) := x in f (Key k) v)
    (⌜ bucket_to_val b = _b ⌝).
Proof.
  intros.
  unfold ITER, FOLD.
  iIntros "%inv #f_spec".
  iModIntro.
  iInduction b as [|[k v] b] "IH" forall (_b); simpl in *;
  iIntros "%ϕ (Hinv & _ & %Hbucket) Hϕ";
  wp_rec; subst; wp_pures.
  - iApply "Hϕ". eauto.
  - wp_apply+ ("IH" with "[] [Hinv]").
    + iModIntro. iIntros.
      iModIntro. iIntros "% (Hinv' & % & %) ?".
      wp_apply+ ("f_spec" with "[Hinv']"); auto.
      iFrame. iSplit; auto. rewrite reverse_cons.
      iPureIntro. by apply prefix_app_r.
    + iFrame. iSplit; eauto. iPureIntro. apply prefix_nil.
    + iIntros "%r (%h & Inv & [%Hcomplete _])".
      wp_pure. iSpecialize ("f_spec" $! (k, v)).
      wp_apply ("f_spec" with "[Inv]").
      { iFrame. iSplit; eauto.
        rewrite reverse_cons.
        by subst. }
      iIntros.
      iApply "Hϕ".
      iExists _. repeat iSplit; eauto.
      simpl. rewrite reverse_cons. by subst.
Qed.

Lemma iter (h f : val) (m : hmap) :
  ITER (permitted m)
    (complete m)
    (Hashtbl h m)
    (λ x, let (k, v) := x in f k v)
    (hashtbl٠iter h)
    .
Proof.
  unfold ITER, FOLD.
  iIntros. iModIntro.
  iIntros. destruct x as [k v].
Admitted.

Lemma remove_spec h m k :
  {{{ Hashtbl h m }}}
    hashtbl٠remove h k
  {{{ RET (); Hashtbl h (rm m k)}}}.
Proof.
Admitted.

Definition Option _o o : iProp :=
  ⌜ option_to_val o = _o ⌝.

Lemma find_opt' h m k :
  {{{ Hashtbl h m }}}
    hashtbl٠find_opt h k
  {{{ v, RET v; Hashtbl h m ∗ ⌜ v = head (m !!! k) ⌝ }}}.
Proof.
Admitted.

Fail Lemma find_opt_fail h m k :
  {{{ Hashtbl h m }}}
    hashtbl٠remove h k
  {{{ v, RET v; Hashtbl h m ∗ ⌜ head (m !!! k) = v ⌝ }}}.

Lemma find_opt h m k :
  {{{ Hashtbl h m }}}
    hashtbl٠find_opt h k
  {{{ _r, RET _r; ∃ (r : option val),
          Option _r r ∗ Hashtbl h m ∗ ⌜ head (m !!! k) = r ⌝ }}}.
Proof.
Admitted.
