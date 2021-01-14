Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.sepcomp.mem_lemmas.

(** * Concurrent Machine Semantics *)

(** NOTE: In the code, we call interaction semantics [CoreSemantics]. *)

(** The [G] type parameter is the type of global environments, the type
    [SCH] is the type of schedules, the type [C] is the type of
    machine states  *)

(** [initial_core] produces the core state corresponding to an entry
   point of a module.  The arguments are the genv, a pointer to the
   function to run, and the arguments for that function. *)

(** [halted] indicates when a machine state has reached a halted state,
   for now this means the schedule ran out. *)

(** [thread_step] is the fundamental small-step relation for the
   sequential semantics. *)

(** [machine_step] is the extern, small-step machine steps. These
    represent the synchronisation primitives and schedule operations. *)

(** The remaining properties give basic sanity properties which constrain
   the behavior of programs. *)
(** -2 a state cannot both step and be halted, and *)

Record ConcurSemantics {G TID SCH TR C M: Type} : Type :=
  { initial_machine : G -> val -> list val -> option C
    ; conc_halted : SCH -> C -> option val
    ; thread_step : G -> SCH -> C -> M -> C -> M -> Prop
    ; machine_step : G -> SCH -> TR -> C -> M -> SCH -> TR -> C -> M -> Prop
    ; runing_thread : C -> TID -> Prop
    ; thread_step_not_halted:
      forall ge  U m q  m' q', thread_step ge U q m q' m' -> conc_halted U q = None
    ; machine_step_not_halted:
        forall ge  U m tr q  U' m' tr' q', machine_step ge U tr q m U' tr' q' m' -> conc_halted U q = None
   } .