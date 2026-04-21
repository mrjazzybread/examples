Require Import Gospel.iris.base.

Require Import
  Stdlib.Floats.Floats
  Stdlib.ZArith.BinIntDef
  Stdlib.Strings.Ascii.

Require Import
  iris.proofmode.proofmode
  iris.heap_lang.proofmode
  iris.heap_lang.notation
  iris.prelude.options.

Local Open Scope Z_scope.

Module Declarations (Heap : H) .

  Module Primitives := Primitives
Heap.

  Import Primitives.

  Import Heap.

  Import Sequence.

  Class _T_sig  := { T : val -> (sequence val) -> iProp }.

  Class _create''_sig  := { create'' : val }.

  Class _create''_spec_sig `{@_create''_sig} `{@_T_sig}  := {
    create''_spec :
      {{{  True  }}} create''  #() {{{  q'' , RET q'';   T q'' empty  }}}
  }.

  Class _clear''_sig  := { clear'' : val }.

  Class _clear''_spec_sig `{@_clear''_sig} `{@_T_sig}  := {
    clear''_spec :
      forall (q'' : val) (q : sequence val), {{{  T q'' q  }}}
      clear''  q''
      {{{ RET #();
        T q'' empty  }}}
  }.

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

  (* Program Value clear'' *)

  Global Declare Instance _clear''_inst : _clear''_sig.

  (* Separation Logic Triple clear''_spec *)

  Global Declare Instance _clear''_spec_inst : _clear''_spec_sig.

End Obligations.