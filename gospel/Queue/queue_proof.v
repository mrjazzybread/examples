Require Import queue_mli.

Require Import
  iris.proofmode.proofmode
  iris.heap_lang.proofmode
  iris.heap_lang.notation
  iris.prelude.options.

Require Import Gospel.iris.base.

Local Open Scope Z_scope.

Module Proofs (Heap : H) : queue_mli.Obligations Heap.

  Module Declarations := Declarations Heap.
  Import Declarations.

  Import Heap.

  Fixpoint Queue' (v : val) (m : sequence val) : iProp :=
    match m with
    |[] => ⌜ v = NONEV ⌝
    |x :: t =>
       ∃ c (next : loc) nextv,
         ⌜ x = c ⌝ ∗
         ⌜ v = (c, #next)%V ⌝ ∗ next ↦ nextv ∗
         Queue' nextv t
  end.

  Definition Queue (v : val) (m : sequence val) : iProp :=
    ∃ (l : loc) q, ⌜ #l = v ⌝ ∗ l ↦ q ∗ Queue' q m.

  Global Instance _T_inst : _T_sig :=
    { T := Queue }.

  (* Provide the necessary typeclass instances *)

  Definition create : val := λ: <>, ref NONEV.

  Global Instance _create''_inst : _create''_sig :=
    { create'' := create }.

  #[refine] Global Instance _create''_spec_inst : _create''_spec_sig := { }.
  Proof.
  Admitted.

End Proofs.
