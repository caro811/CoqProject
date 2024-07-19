(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Export State.

Section Actions.

(* Action *)
Inductive action : Set :=
          | read (va: vadd)               : action
          | write (va: vadd) (val: value) : action
          | chmod                         : action.

(*********************************************************************************)
(* Pre y post condiciones *)

Definition is_RW (s: state) (ma: madd) : Prop :=
              exists (p: page), Some p = (memory s) ma
           /\ exists (v: option value), RW v = page_content p.

(*****************************)
(* read *)
Definition read_pre (va: vadd) (s: state) : Prop :=
              os_accessible va
           /\ aos_activity s = running
           /\ (exists (ma: madd), va_mapped_to_ma s va ma
                               /\ is_RW s ma).

Definition read_post (va: vadd) (s: state) (s': state) : Prop :=
              s = s'.

(*****************************)
(* write *)
Definition write_pre (va: vadd) (val: value) (s: state) : Prop :=
              os_accessible va
           /\ aos_activity s = running
           /\ (exists (ma: madd), va_mapped_to_ma s va ma
                               /\ is_RW s ma).

Definition write_post (va: vadd) (val: value) (s: state) (s': state) : Prop :=
              exists (ma: madd), va_mapped_to_ma s va ma
           /\ (memory s') ma = Some {| page_content  := RW (Some val);
                                       page_owned_by := Os (active_os s) |}
           (** /\ (forall (ma': madd), ma' <> ma -> (memory s') ma' = (memory s) ma') **)
           (** No hace falta porque esta incluido en differ_at_most_memory  s s' ma.  **)
           /\ differ_at_most_memory s s' ma.

(*****************************)
(* chmod *)
Definition chmod_pre (s: state) : Prop :=
              aos_activity s = waiting
           /\ (exists (o: os), Some o = (oss s) (active_os s)
                            /\ hcall o = None).

Definition chmod_post (s: state) (s': state) : Prop :=
              (trusted_os (active_os s) /\ active_os s' = active_os s
                                        /\ aos_exec_mode s' = svc
                                        /\ aos_activity s' = running
                                        /\ oss s' = oss s
                                        /\ hypervisor s' = hypervisor s
                                        /\ memory s' = memory s)
           \/ (~trusted_os (active_os s) /\ active_os s' = active_os s
                                         /\ aos_exec_mode s' = usr
                                         /\ aos_activity s' = running
                                         /\ oss s' = oss s
                                         /\ hypervisor s' = hypervisor s
                                         /\ memory s' = memory s).

(******************************************)
(* Todas *)
Fixpoint Pre (s: state) (a: action) {struct a} : Prop :=
         match a with
         | read va      => read_pre va s
         | write va val => write_pre va val s
         | chmod        => chmod_pre s
         end.

Fixpoint Post (s: state) (a: action) (s': state) {struct a}: Prop :=
         match a with
         | read va      => read_post va s s'
         | write va val => write_post va val s s'
         | chmod        => chmod_post s s'
         end.

End Actions.
