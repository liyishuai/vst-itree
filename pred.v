From Coq Require Import
     ExtrOcamlIntConv.
From ExtLib Require Import
     Monad.
From SimpleIO Require Import
     SimpleIO.
From ITree Require Import
     Traces
     ITree.
From VST Require Import
     proofauto.

Instance MonadIter_IO : MonadIter IO :=
  fun _ _ f =>
    IO.fix_io (fun self x =>
      IO.bind (f x) (fun y =>
      match y with
      | inl x' => self x'
      | inr r => IO.ret r
      end)).

Inductive is_vis_trace {InvisE VisE : Type -> Type} {R : Type}:
  itree (InvisE +' VisE) R -> @trace VisE R -> Prop  :=
| Trace_Empty (t : itree (InvisE +' VisE) R):
    is_vis_trace t (TEnd : trace)
| Trace_Ret (r : R): is_vis_trace (ret r) (TRet r)
| Trace_Tau (t : itree (InvisE +' VisE) R) (l : trace):
    is_vis_trace t l -> is_vis_trace (Tau t) l
| Trace_Invis (X : Type) (e : InvisE X) (k : X -> itree (InvisE +' VisE) R)
              (x : X) (l : trace):
    is_vis_trace (k x) l ->
    is_vis_trace (Vis (inl1 e) k) l
| Trace_Vis (X : Type) (f : VisE X) (k : X -> itree (InvisE +' VisE) R)
            (x : X) (l : trace):
    is_vis_trace (k x) l ->
    is_vis_trace (Vis (inr1 f) k) (TEventResponse f x l).

Definition vis_trace_incl
           {E F : Type -> Type} {R : Type}
           (t1 t2 : itree (E +' F) R) :=
  forall (tr : trace),
    is_vis_trace t1 tr -> is_vis_trace t2 tr.

(** The following definitions can each compile, but breaks the other: *)

Definition execute {E T} (m : itree E T) : IO T :=
  interp (M := IO) (fun _ _ => exit int_zero) m.

Definition ITREE {E F T} (t : itree (E +' F) T) :=
  EX t' : itree (E +' F) T, !! vis_trace_incl t t' && has_ext t'.
