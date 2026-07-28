Require Export hashtbl__types hashtbl__code.

From zoo Require Import
  prelude.

From zoo_std
  Require Import array option list bqueue for_.

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

Implicit Types ℓ : location.

Fixpoint Bucket (_b : val) (b : bucket) : iProp :=
  match b with
  |[] => ⌜ _b = §Nil%V ⌝
  |cons x t =>
     let (k, v) := x in
     ∃ ℓ _t, ⌜ _b = #ℓ ⌝ ∗ ℓ ↦ₕ Header §Cons 3 ∗ ℓ.[key] ↦ Key k ∗
          ℓ.[data] ↦ v ∗ ℓ.[next] ↦ _t ∗ Bucket _t t
  end.

Fixpoint remove_assoc (k : K) (l : bucket) :=
  match l with
  |[] => []
  |(k', v) :: t =>
     if (decide (k = k'))
     then t
     else
       (k', v) :: remove_assoc k t
  end.

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
  {{{ ⌜ n >= 0 ⌝ }}}
    hashtbl٠index (Key k) #n
  {{{ r, RET #r; ⌜ r = indexZ k n ⌝ }}}.
Proof.
  iIntros "%ϕ % Hϕ".
  wp_rec. wp_pures.
  wp_apply (hashtbl٠hash_spec with "[//]").
  iIntros. wp_pures.
  iApply "Hϕ". iPureIntro.
  pose (hash_nonneg k). subst.
  apply Z_rem_mod; lia.
Qed.

Lemma indexZ_range :
  ∀ A k (l : list A), length l > 0 -> valid (indexZ k (length l)) l.
Proof.
  intros.
  pose (hash_nonneg k).
  lia.
Qed.

Hint Resolve
  indexZ_range : zarith.

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

Implicit Types _k _v : val.

Fixpoint Tbl vs l : iProp :=
  match l with
  |[] => ⌜ vs = [] ⌝
  |b :: t => ∃ _b xs,
    ⌜ vs = _b :: xs ⌝ ∗ Bucket _b b ∗ Tbl xs t
end.

Definition HashtblArray (h : val) (m : hmap) : iProp :=
  ∃ (v : list val) tbl n, array_model h (DfracOwn 1) v ∗
           Tbl v tbl ∗
           ⌜ n = len tbl ⌝ ∗ ⌜0 < n⌝%Z ∗
           ⌜ no_garbage n tbl ⌝ ∗ ⌜ valid_buckets n tbl m ⌝.

Definition Hashtbl (h : val) (m : hmap) : iProp :=
  ∃ ℓ arr (c : Z),
    ⌜ h = #ℓ ⌝ ∗ ℓ.[buckets] ↦ arr ∗ HashtblArray arr m
  ∗ ℓ.[size] ↦ #c ∗ ⌜ c = cardinality m ⌝.

Ltac iPack :=
  repeat (try iSplit; (try iExists _)); try iPureIntro.

Lemma replicate_model (n : Z) :
  True -∗
  Tbl (replicate n (§Nil)%V) (replicate n []).
Proof.
Admitted.

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
  iFrame. iPack; eauto.
  - by iApply replicate_model.
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

Lemma Tbl_len vs tbl :
  Tbl vs tbl -∗
    Tbl vs tbl ∗ ⌜ len vs = len tbl ⌝.
Proof.
  iIntros "Tbl". iInduction tbl as [|h t Ih] forall (vs); simpl Tbl.
  + iDestruct "Tbl" as "%". by subst.
  + iDestruct "Tbl" as "(% & % & % & ? & Tbl)".
    subst. length.
    iSpecialize ("Ih" $! xs).
    iApply "Ih" in "Tbl".
    iDestruct "Tbl" as "(? & <-)".
    by iFrame.
Qed.

Ltac destructHashtblArray H :=
  iDestruct H as "(%vs & %tbl & % & Harray & (Htbl & % & % & % & %))".

Lemma listz_insert_cons_r {A} (i : Z) l (x : A) y:
  (0 < i) → <[i:=x]> (y :: l) = y :: <[(i - 1):=x]> l.
Proof.
  intros.
  unfold insert, list_insert, listz_insert.
  rewrite decide_False; try lia.
  rewrite insert_cons_r; try lia.
  destruct decide; repeat f_equal; lia.
Qed.

Lemma Tbl_peek _tbl tbl b i :
    Tbl _tbl tbl -∗
    ⌜ b = tbl !!! i ⌝ -∗
    ⌜ valid i _tbl ⌝ -∗
    (Bucket (_tbl !!! i) b ∗
       (Bucket (_tbl !!! i) b -∗ Tbl _tbl tbl)).
Proof.
  iIntros "Htbl Hb Hv".
  iPoseProof (Tbl_len _tbl tbl with "Htbl") as "[Htbl %H]".
  rewrite H. clear H.
  iInduction tbl as [|x t Ih] forall (i b _tbl);
    iDestruct "Hb" as "%"; iDestruct "Hv" as "%";
    length in *; try lia.
  iSimpl in "Htbl".
  iDestruct "Htbl" as "(% & % & % & ? & ?)".
  subst _tbl.
  destruct (decide (i = 0)).
  - subst i b.
    do 2 rewrite lookup_total_cons_eq_0.
    iFrame. iIntros. by iFrame.
  - iDestruct ("Ih" with "[] [] [$]") as "[Hb Htail]".
    + iPureIntro.
      by rewrite lookup_total_cons_ne_0 in H.
    + iPureIntro. lia.
    + subst b. do 2 (rewrite lookup_total_cons_ne_0; try lia).
      iFrame. iIntros.
      simpl. iFrame. iExists _. iSplit; eauto. by iStep.
Qed.

Lemma insert_Tbl vs tbl ℓ k v b i :
  ⌜ valid i vs ⌝ -∗
  ⌜ b = tbl !!! i ⌝ -∗
  Tbl vs tbl -∗
  ℓ.[key] ↦ Key k -∗
  ℓ.[data] ↦ v -∗
  ℓ.[next] ↦ (vs !!! i) -∗
  ℓ ↦ₕ Header §Cons 3 -∗
  Tbl (<[i:=#ℓ]> vs) (<[i:=(k, v) :: b]> tbl).
Proof.
  iIntros "Hv Hb Htbl ? ? Hnext ?".
  iInduction tbl as [|x t Ih] forall (i b vs);
    iDestruct "Hv" as "%"; iDestruct "Hb" as "%".
  - length in *. iDestruct "Htbl" as "%".
    subst. by do 2 (rewrite list_insert_ge; try (length; lia)).
  - destruct (decide (i = 0)).
    { subst. simpl. iFrame.
      iDestruct "Htbl" as "(% & % & % & ? & ?)".
      subst vs. iFrame. iExists _. repeat iSplit; eauto. }
    simpl. iDestruct "Htbl" as "(% & % & -> & ? & Htbl)".
    do 2 (rewrite listz_insert_cons_r; try lia).
    simpl. iFrame.
    iExists _. iSplit; eauto.
    iApply ("Ih" with "[] [] [$] [$] [$] [Hnext] [$]").
    + iPureIntro. length in *. lia.
    + by rewrite lookup_total_cons_ne_0 in H0; try lia.
    + by rewrite lookup_total_cons_ne_0; try lia.
Qed.

Lemma add'_spec h m k v :
     {{{ HashtblArray h m }}}
       hashtbl٠add' h (Key k) v
     {{{ RET (); HashtblArray h (_add m k v)}}}.
Proof.
  iIntros "%ϕ S Hϕ".
  wp_rec.
  destructHashtblArray "S".
  iPoseProof (Tbl_len vs tbl with "Htbl") as "[Htbl %]".
  wp_apply+ (array٠size𑁒spec with "Harray") as "Harray".
  wp_pures.
  wp_apply+ (hashtbl٠index_spec).
  { iPureIntro. lia. }
  iIntros.
  wp_pures. wp_apply+ (array٠get𑁒spec with "[Harray]") as "[% Harray]".
  { iFrame. iPureIntro. intros. rewrite list_lookup_alt. split; auto. }
  iSteps. iModIntro.
  wp_apply+ (array٠set𑁒spec with "Harray") as "Harray".
  iApply "Hϕ". iFrame.
  iExists (<[r:=(k, v) :: tbl !!! r]> tbl), _.
  iPack; list; eauto with lia.
  - iApply (insert_Tbl with "[//] [//] [$] [$] [$] [$] [$]").
  - apply no_garbage_insert; eauto. subst. rewrite H3. by list.
  - apply valid_buckets_insert; auto with lia.
    subst. by rewrite H3.
Qed.

Definition ITER {A}
  (permitted : list A -> Prop)
  (complete : list A -> Prop)
  (S : iProp)
  (body : expr)
  (loop : A -> expr)
  :=
  ∀ inv,
    (∀ (x : A) (h1 : list A) (h2 : list A),
       {{{ inv h1 ∗ ⌜ h2 = h1 ++ {[x]} ⌝ ∗ ⌜ permitted h2 ⌝ }}}
       loop x
       {{{ RET (); inv h2 }}}) -∗
  {{{ inv [] ∗ ⌜ permitted [] ⌝ ∗ S }}}
    body
  {{{ RET (); ∃ h, inv h ∗ ⌜ complete h ⌝ ∗ S }}}.

Lemma bucket_iter_right_spec (_b : val) b (f : val) :
  ITER (λ h, h `prefix_of` reverse b)
    (λ h, h = reverse b)
    (Bucket _b b)
    (hashtbl٠bucket_iter_right _b f)
    (λ (x : K * val), let (k, v) := x in f (Key k) v).
Proof.
  intros.
  unfold ITER.
  iIntros "%inv #f_spec".
  iModIntro.
  iInduction b as [|[k v] b] "IH" forall (_b); simpl in *;
  iIntros "%ϕ (Hinv & _ & Hbucket) Hϕ";
  wp_rec; subst; wp_pures.
  - iDestruct "Hbucket" as "%". subst.
    wp_pures. iApply "Hϕ". eauto.
  - iDestruct "Hbucket" as "(% & % & % & ? & ? & ? & ? & Hb)".
    subst. do 3 iStep. iIntros "!> _". wp_load.
    wp_apply+ ("IH" with "[] [Hinv $Hb] ").
    + iIntros "!>**!>% (Hinv' & % & %) ?".
      wp_apply+ ("f_spec" with "[Hinv']"). 2: auto.
      iFrame. rewrite reverse_cons.
      iSplit; auto.
      iPureIntro.
      by apply prefix_app_r.
    + iFrame.
      iPureIntro. apply prefix_nil.
    + iIntros "(%h & Inv & [%Hcomplete ?])".
      wp_pure. iSpecialize ("f_spec" $! (k, v)).
      do 2 wp_load.
      wp_apply ("f_spec" with "[Inv]").
      { iFrame. iSplit; eauto.
        rewrite reverse_cons.
        by subst. }
      iIntros.
      iApply "Hϕ". iFrame.
      repeat iSplit; eauto. iFrame.
      rewrite reverse_cons. by subst.
Qed.

Definition complete_key (k : K) (xs : hmap) (history : list (K * val)) :=
  map snd (filter_key k history) = reverse (xs !!! k).

Definition complete xs h := ∀ k, complete_key k xs h.

Definition permitted (xs : hmap) history :=
    ∀ k, map snd (filter_key k history) `prefix_of` (reverse (xs !!! k)).

Definition inv_array_reached n m :=
  λ h (i : Z),
         (forall k,
             indexZ k n < i → complete_key k m h).

Definition inv_array_unreached n (m : hmap) :=
  λ (h : list (K * val)) (i : Z),
    (forall k v,
        indexZ k n >= i → (k, v) ∉ h).

Definition inv_array inv arr (l : list val) tbl m (_ : Z) i : iProp :=
  ∃ h, inv h ∗
         array_model arr (DfracOwn 1) l ∗
         Tbl l tbl ∗
         ⌜ inv_array_reached (len l) m h i ⌝ ∗
         ⌜ inv_array_unreached (len l) m h i ⌝.

Definition inv_bucket m h inv b : iProp :=
  ∀ h', ⌜ h' = h ++ b ⌝ -∗
    inv h' ∗ ⌜ permitted m h' ⌝.

Lemma reverse_map :
  forall {A B} (l : list A) (f : A -> B),
    reverse (map f l) = map f (reverse l).
Proof.
  intros.
  induction l as [|h t Ih]. auto.
  simpl. do 2 rewrite reverse_cons.
  rewrite map_app. by rewrite Ih.
Qed.

Lemma prefix_map :
  forall A B (l1 : list A) (l2 : list A) (f : A -> B),
    l1 `prefix_of` l2 →
    map f l1 `prefix_of` map f l2.
Proof.
  intros ????? [??].
  eexists.
  rewrite <- map_app.
  by f_equal.
Qed.

Lemma prefix_filter :
  forall (l1 : bucket) (l2 : bucket) k,
    l1 `prefix_of` l2 →
    filter_key k l1 `prefix_of` filter_key k l2.
Proof.
  induction l1 as [|h t Ih];
    intros l2 k [l3 H1]. apply prefix_nil.
  rewrite H1.
  rewrite filter_cons. simpl.
  case_decide.
  + rewrite filter_cons_True; auto.
    apply prefix_cons. apply Ih.
    by apply prefix_app_r.
  + rewrite filter_cons_False; auto.
    apply Ih. by apply prefix_app_r.
Qed.

Lemma permitted_add_next :
  ∀ n k v b tbl i m h h' h'',
    valid i tbl →
    b = tbl !!! i →
    (forall k', indexZ k' n >= i → filter_key k' h = []) →
    valid_buckets n tbl m →
    no_garbage n tbl →
    h' ++ {[(k, v)]} = h'' →
    h'' `prefix_of` reverse b →
    permitted m (h ++ h') →
    permitted m (h ++ h' ++ [(k, v)]).
Proof.
  intros n k v b l i m h h' h''
    HvalidI Hb Hfilterk'
    Hvalid Hgarbage Hh' Hprefix Hpermitted k'.
    assert (A1: (k, v) ∈ (l !!! i)).
  { apply elem_of_reverse.
    apply elem_of_prefix with (l1:= h''); subst; auto.
    apply elem_of_app. right.
    by apply list_elem_of_singleton. }
  assert (A2 : indexZ k n = i).
  { apply Hgarbage with v; auto. }
  destruct (decide (indexZ k' n = i)) as [E | E].
  { rewrite filter_app. rewrite map_app.
    rewrite filter_app.
    rewrite Hfilterk'; try lia.
    list. rewrite <- filter_app.
    unfold valid_buckets in *.
    erewrite Hvalid; auto.
    rewrite reverse_map.
    rewrite <- filter_reverse.
    apply prefix_map.
    apply prefix_filter.
    subst. by rewrite E. }
  { rewrite app_assoc. rewrite filter_app.
    rewrite filter_cons_False.
    - intros ?. by subst.
    - list. apply Hpermitted. }
Qed.

Lemma permitted_start_next :
  ∀ n j h m,
  (∀ k v, indexZ k n >= j → (k, v) ∉ h) →
  (∀ k : K, indexZ k n < j → complete_key k m h) →
  permitted m h.
Proof.
  intros n j h m H1 H2 k.
  destruct (decide (indexZ k n < j)).
  + by rewrite H2.
  + assert (Hempty: filter_key k h = []).
    { apply filter_key_nin. intros. auto with lia. }
    rewrite Hempty. apply prefix_nil.
Qed.

Lemma inv_array_reached_preserve :
  ∀ tbl n m h j j' b,
    j' = (j + 1)%Z ->
    valid j tbl ->
    no_garbage n tbl ->
    valid_buckets n tbl m ->
    inv_array_reached n m h j ->
    inv_array_unreached n m h j ->
    b = (tbl !!! j) ->
    inv_array_reached n m (h ++ reverse b) j'.
Proof.
  unfold inv_array,
    inv_array_unreached, inv_array_reached.
  intros tbl n m h j j' b
    ?? NG Hvalid Hcomplete Hunreached **.
  unfold complete_key.
  rewrite filter_app.
  set (i':=indexZ k n).
  destruct (decide (i' = j)); subst.
  { rewrite filter_key_nin; auto with lia.
    simpl. rewrite filter_reverse.
    rewrite <- reverse_map. f_equal.
    erewrite Hvalid; auto. }
  { erewrite filter_key_nin with (b:=reverse _).
    - list. apply Hcomplete. lia.
    - intros v. rewrite elem_of_reverse.
      intro Hnin. apply NG in Hnin; lia. }
Qed.

Hint Resolve not_elem_of_nil : rlist.
Ltac rlist := auto with rlist.


Ltac intro_iter :=
  unfold ITER;
  iIntros "%inv #f_spec !> %ϕ
           (Hinv & %Hpermitted & S) Hϕ".

Hint Rewrite
  @list_lookup_alt : clist.

Lemma iter_aux_spec (arr f : val) (m : hmap) :
  ITER (permitted m)
    (complete m)
    (HashtblArray arr m)
    (hashtbl٠iter_aux arr f)
    (λ x, let (k, v) := x in f (Key k) v).
Proof.
  intro_iter.
  wp_rec. wp_pures.
  destructHashtblArray "S".
  wp_apply+ (array٠size𑁒spec with "Harray") as "Harray".
  iPoseProof (Tbl_len vs tbl with "Htbl") as "[Htbl %]".
  wp_apply+ (for𑁒spec (inv_array inv arr vs tbl m) 0 (len vs) with "[Hinv Harray Htbl]"). 1: lia. iSplit.
  (* The invariant holds at the start of iteration *)
  + iFrame. iPureIntro. split; auto; intros ?**; rlist.
    pose (hash_nonneg k). lia.
  + iIntros "!> % % % %".
    iIntros "(%h & Hinv & Harray & Htbl & (% & %Hunreached))".
    wp_pures. wp_apply+ (array٠get𑁒spec with "[Harray]").
    { iFrame. iIntros. rewrite list_lookup_alt. by list. }
    iIntros "(% & Harray)".
    (* When applying the spec for [bucket_iter_right], we must prove:
       - The correctness of the nested triple.  This is a persistent
         statement meaning that it does not require any resources
       - The precondition of the triple.  This requires assertion [Hinv], the loop invariant.
       - The post condition of the function.  This requires assertion
         [Harray], the ownership of the array. *)
    (* We apply [bucket_iter_right_spec] with the model of the bucket
       we are iterating over and the proper invariant. *)
    iDestruct (Tbl_peek vs tbl (tbl !!! i) i with "[$] [//] [//]")
      as "[B Htbl]".
    iApply (bucket_iter_right_spec _
              (tbl !!! i) _ (inv_bucket m h inv) with "[] [Hinv B] [Harray Htbl]").
    (* The correctness of the triple *)
    { iIntros "%%%!>%ϕ' (Hinv & % & %) Hϕ".
      iDestruct ("Hinv" $! (h ++ h1) with "[%//]")
        as "[Hinv %]".
      wp_apply ("f_spec" with "[Hinv]").
      + iFrame. iSplit; eauto.
        iPureIntro. list. destruct x.
        eapply permitted_add_next; eauto.
        3: rewrite <- H8. all: eauto.
        { lia. }
        intros. apply filter_key_nin.
        intros. apply Hunreached.
        rewrite H3. subst. lia.
      + list. iIntros.
        iApply "Hϕ". unfold inv_bucket.
        iIntros. subst. iFrame.
        iPureIntro. destruct x.
        eapply permitted_add_next; eauto. 1: lia.
        intros. apply filter_key_nin. intros.
        apply Hunreached. rewrite H3. by length. }
    (* The precondition of [bucket_iter_right] *)
    { unfold inv_bucket.
      - list. iFrame. iSplit.
        2: { iPureIntro. apply prefix_nil. }
        iIntros. subst h'.
        iFrame. iPureIntro.
        eapply permitted_start_next; eauto. }
    (* The invariant is maintained while iterating over each bucket. *)
    { iIntros "!> (%h' & H1 & % & ?)".
      iSplit. 1: auto.
      iDestruct ("Htbl" with "[$]") as "?".
      iDestruct ("H1" with "[//]") as "[H1 %]".
      iFrame. iSplit; iPureIntro.
      - subst h'. rewrite H3.
        eapply inv_array_reached_preserve;
          eauto with f_equal; try lia; subst; auto; by rewrite <- H3.
      - intros ?**. rewrite not_elem_of_app. split.
        + apply Hunreached. lia.
        + subst h'.
          rewrite elem_of_reverse.
          intros Hnin. subst.
          apply H1 in Hnin; try lia.
          length in *. rewrite <- H3 in Hnin. lia. }
  (* The post condition holds after iteration is complete. *)
  + iIntros "(%h & ? & ? & ? & %)". iApply "Hϕ".
    iFrame. repeat iSplit; iPureIntro; auto.
    - intro. apply H4. lia.
    - pack; eauto; subst; by rewrite H3.
Qed.

Lemma iter_rev_spec h (f : val) m :
  ITER (permitted m)
    (complete m)
    (Hashtbl h m)
    (hashtbl٠iter_rev h f)
    (λ x, let (k, v) := x in f (Key k) v).
Proof.
  unfold ITER.
  iIntros "%inv #f_spec !> %ϕ
           (Hinv & %Hpermitted &
           %lh & %arr & %card & %H1 & ? & S & ? & ?) Hϕ".
  subst h. wp_rec.
  wp_load.
  wp_apply+ (iter_aux_spec with "[] [Hinv S]"); try (by iFrame).
  iIntros "(% & ? & ? & ?)".
  iApply "Hϕ". iPack. by iFrame.
Qed.

(* Invariant for [resize] *)
Definition resize_inv new_arr (h : list (K * val)) : iProp :=
  ∃ m,
    HashtblArray new_arr m ∗
      ⌜ ∀ k, map snd (filter_key k h) = reverse (m !!! k) ⌝.

Ltac eq_decide v1 v2 := destruct (decide (v1 = v2)).

Lemma resize_inv_step :
  forall k v k' (l : list (K * val)) b x,
    (∀ k, map snd (filter_key k b) = reverse (x !!! k)) ->
    l = (filter_key k' (b ++ [(k, v)])) ->
    map snd l = reverse (_add x k v !!! k').
Proof.
  intros k v k' l **.
  subst l.
  rewrite filter_app.
  eq_decide k k'.
  { subst. rewrite add_lookup_eq.
    rewrite reverse_cons.
    rewrite map_app. filter. simpl. by f_equal. }
  { rewrite add_lookup_neq; auto. filter. by list. }
Qed.

Ltac destructHashtbl H :=
  set (x := ("(%lh & %arr & %card & %H1 & H2 & " ++ H ++ " & H3 & %)")%string);
  iDestruct H as x;
  destructHashtblArray H.

Lemma hashtbl_extensionality h m1 m2 :
  ⌜∀ k, m1 !!! k = m2 !!! k⌝ -∗
  Hashtbl h m1 -∗
  Hashtbl h m2.
Proof.
  iIntros "%Helts S".
  destructHashtbl "S".
  unfold Hashtbl. iPack; eauto; iFrame.
  iPack. 1: apply H0. all: eauto.
  + unfold valid_buckets. intros.
    rewrite <- Helts. eauto.
  + by erewrite cardinality_extensionality.
Qed.

Lemma reverse_injective :
  forall A (l1 : list A) (l2 : list A),
    reverse l1 = reverse l2 ->
    l1 = l2.
Proof.
  intros.
  rewrite <- reverse_involutive.
  rewrite <- reverse_involutive with (l:=l1).
  auto with f_equal.
Qed.

Lemma resize_spec (h : val) m :
  {{{ Hashtbl h m }}}
    hashtbl٠resize h
  {{{ RET (); Hashtbl h m }}}.
Proof.
  intro ϕ.
  iIntros "S Hϕ".
  wp_rec. destructHashtbl "S".
  subst h. wp_load.
  wp_apply (array٠size𑁒spec with "[Harray //]").
  iPoseProof (Tbl_len vs tbl with "Htbl") as "[Htbl %]".
  iIntros "Harray". wp_pures. wp_apply (array٠make_spec).
  { iPureIntro. lia. }
  iIntros "%new_arr Hnew". wp_pures.
  wp_load.
  wp_apply+ (iter_aux_spec _ _ m (resize_inv new_arr) with "[] [$Harray $Hnew $Htbl] [H2 H3 Hϕ]").
  - assert (n = len vs). { lia. }
    clear dependent tbl ϕ.
    iIntros "%kv %h1 %h2 !> %ϕ ((% & S & %) & % & %) Hϕ".
    destruct kv. wp_pures. wp_apply (add'_spec with "[$S]").
    iIntros. iApply "Hϕ".
    iFrame. auto.
    iPureIntro. intros. eapply resize_inv_step; subst; eauto.
  - iSplitL; iPack; try iFrame.
    1: by iApply replicate_model.
    10: eauto. (* Try to find a way around this. *)
    all: eauto.
    + length. lia.
    + intros ????. do 2 list in *. intro Helem.
      by apply not_elem_of_nil in Helem.
    + intros ?**. do 2 list in *. erewrite lookup_total_empty.
      by subst.
    + intros. filter.
      by rewrite lookup_total_empty.
    + intro. filter. apply prefix_nil.
  - iIntros "!> (% & (%m' & ? & %) & %Hcomplete & ?)".
    wp_store. iStep.
    assert (A : ∀ k : K, m !!! k = m' !!! k).
    { intro k. apply reverse_injective.
      by rewrite <- Hcomplete. }
    iApply (hashtbl_extensionality _ m' m); auto.
    do 2 iStep. iFrame. by erewrite cardinality_extensionality.
Qed.

Lemma hashtbl٠population_spec h m :
  {{{ Hashtbl h m }}}
    hashtbl٠population h
  {{{ (c : Z), RET #c; Hashtbl h m ∗ ⌜ c = cardinality m ⌝ }}}.
Proof.
  iIntros "%ϕ S Hϕ".
  destructHashtbl "S".
  wp_rec. subst h. wp_load. iModIntro.
  iSpecialize ("Hϕ" $! card). iApply "Hϕ".
  iFrame. iPack. 5: eauto. all: eauto.
Qed.

Lemma hashtbl٠inc_pop_spec h ℓ (arr : val) m (card : Z) :
  {{{ ⌜ h = #ℓ ⌝ ∗ ℓ.[size] ↦ #card ∗ ℓ.[buckets] ↦ arr ∗
        HashtblArray arr m ∗
        ⌜ card = cardinality m - 1 ⌝ }}}
    hashtbl٠inc_pop h
   {{{ RET (); Hashtbl h m }}}.
Proof.
  iIntros "%ϕ (% & pop & buck & S & %) ?".
  wp_rec. subst h. wp_load. wp_store.
  wp_apply+ (hashtbl٠population_spec with "[$S $pop $buck]")
    as "%c (S & %)".
  { iSplit; auto. iPureIntro. lia. }
  subst card. clear arr.
  destructHashtbl "S".
  rewrite H1. wp_load.
  wp_apply (array٠size𑁒spec with "[$Harray]") as "Harray".
  wp_pures. destruct bool_decide; wp_pures.
  2: iSteps. unfold Hashtbl.
  wp_apply (resize_spec with "[H2 H3 $Harray $Htbl]"); iSteps.
Qed.

Lemma hashtbl٠add_spec h m k v :
  {{{ Hashtbl h m }}}
    hashtbl٠add h (Key k) v
  {{{ RET (); Hashtbl h (_add m k v) }}}.
Proof.
  iIntros "%ϕ (% & % & % & % & Harr & S & Hsize & %) Hϕ". subst h.
  wp_rec. wp_pures. wp_load.
  wp_apply+ (add'_spec with "[$S]").
  iIntros "S". wp_pures.
  wp_apply+ ((hashtbl٠inc_pop_spec _ ℓ arr _) with "[$Harr $Hsize S]").
  { iSteps. erewrite cardinality_add; eauto.
    subst c. iPureIntro. lia. }
  iApply "Hϕ".
Qed.

End spec.
