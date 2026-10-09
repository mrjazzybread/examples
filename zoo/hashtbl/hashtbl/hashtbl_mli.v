Require Import Gospel.iris.base.

Require Import
  Stdlib.Floats.Floats
  Stdlib.ZArith.BinIntDef
  Stdlib.Strings.Ascii.

Require Import
  zoo.prelude
  zoo.diaframe.diaframe
  zoo.language.notations
  zoo.language.typeclasses
  zoo.language.notations.

Local Open Scope Z_scope.

Module Declarations (Heap : H) .

  Module Primitives := Primitives
Heap.

  Import Primitives.

  Import Heap.

  Import Fin_maps.

  Class _T_sig  := {
    T :
      forall {K} {V}, val ->
      (val -> K -> iProp) ->
      (val -> V -> iProp) ->
      (fin_map K (sequence V)) ->
      iProp
  }.

  Class _create''_sig  := { create'' : val }.

  Class _create''_spec_sig `{@_create''_sig} `{@_T_sig}  := {
    create''_spec :
      forall {V} {K}, forall
      `{Inhabited V}
      `{Inhabited K}
      (n'' : val)
      (n : integer)
      (V' : val -> V -> iProp)
      (K' : val -> K -> iProp),
      {{{  Int  n'' n ∗⌜ n > 0 ⌝  }}}
      create''  n''
      {{{  h'' , RET h'';
        Int  n'' n ∗T  h'' K' V' (__empty (V := sequence V) (K := K))   }}}
  }.

  Class _add''_sig  := { add'' : val }.

  Class _add''_spec_sig `{@_add''_sig} `{@_T_sig}  := {
    add''_spec :
      forall {V} {K}, forall
      `{Inhabited V}
      `{Inhabited K}
      (h'' : val)
      (h : fin_map K (sequence V))
      (k'' : val)
      (k : K)
      (v'' : val)
      (v : V)
      (V' : val -> V -> iProp)
      (K' : val -> K -> iProp),
      {{{  T  h'' K' V' h ∗K'  k'' k ∗V'  v'' v   }}}
      add''  h'' k'' v''
      {{{ RET ();

      ∃ (_k' : val) (_v' : val),
      T  h'' K' V' (add k (Sequence.cons v (__seq_get h k)) h) ∗Val
       k'' _k' ∗Val  v'' _v'

       }}}
  }.

  Class _find''_sig  := { find'' : val }.

  Class _find''_spec_sig `{@_find''_sig} `{@_T_sig}  := {
    find''_spec :
      forall {V} {K}, forall
      `{Inhabited V}
      `{Inhabited K}
      (h'' : val)
      (h : fin_map K (sequence V))
      (k'' : val)
      (k : K)
      (V' : val -> V -> iProp)
      (K' : val -> K -> iProp),
      {{{  T  h'' K' V' h ∗K'  k'' k   }}}
      find''  h'' k''
      {{{  v'' , RET v'';
        T  h'' K' V' h ∗K'  k'' k ∗V'  v'' (Sequence.hd (__seq_get h k))   }}}
  }.

  Definition cardinality {V} {K} `{@Inhabited V} `{@Inhabited K} (m : fin_map K (sequence V))
  : integer :=
    fold (fun (k : K)
    =>
    fun (s : sequence V) => fun (acc : integer) => acc + (Sequence.length s)) 0 m.

  Class _population''_sig  := { population'' : val }.

  Class _population''_spec_sig `{@_population''_sig} `{@_T_sig}  := {
    population''_spec :
      forall {V} {K}, forall
      `{Inhabited V}
      `{Inhabited K}
      (h'' : val)
      (h : fin_map K (sequence V))
      (V' : val -> V -> iProp)
      (K' : val -> K -> iProp),
      {{{  T  h'' K' V' h   }}}
      population''  h''
      {{{  n'' , RET n'';
        T  h'' K' V' h ∗Int  n'' (cardinality h)   }}}
  }.

  Class _iter_rev''_sig  := { iter_rev'' : val }.

End Declarations.

Module Type Obligations (Heap : H) .

  Module Declarations := Declarations
Heap.

  Import Declarations.

  (* Lens T *)

  Global Declare Instance _T_inst : _T_sig.

  (* Program Value create'' *)

  Global Declare Instance _create''_inst : _create''_sig.

  (* Separation Logic Triple create''_spec *)

  Global Declare Instance _create''_spec_inst : _create''_spec_sig.

  (* Program Value add'' *)

  Global Declare Instance _add''_inst : _add''_sig.

  (* Separation Logic Triple add''_spec *)

  Global Declare Instance _add''_spec_inst : _add''_spec_sig.

  (* Program Value find'' *)

  Global Declare Instance _find''_inst : _find''_sig.

  (* Separation Logic Triple find''_spec *)

  Global Declare Instance _find''_spec_inst : _find''_spec_sig.

  (* Program Value population'' *)

  Global Declare Instance _population''_inst : _population''_sig.

  (* Separation Logic Triple population''_spec *)

  Global Declare Instance _population''_spec_inst : _population''_spec_sig.

  (* Program Value iter_rev'' *)

  Global Declare Instance _iter_rev''_inst : _iter_rev''_sig.

End Obligations.