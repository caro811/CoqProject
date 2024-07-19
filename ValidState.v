(*******************************************************************
 * Este archivo especifica las propiedades de valid state.
 ******************************************************************)

Require Export Actions.

Section ValidState.

(* Propiedades de valid state *)

(* Propiedad 3 *)
(* Si el hypervisor o un OS confiable esta corriendo, el procesador debe estar en modo
   supervisor. *)
Definition VSprop3 (s: state) : Prop :=
              (aos_activity s = waiting \/ trusted_os (active_os s))
           -> aos_exec_mode s = svc.

(* Propiedad 5 *)
(* El hypervisor mapea una direccion fisica de un OS a una direccion de maquina perteneciente
   al mismo OS. *)
Definition VSprop5 (s: state) : Prop :=
              forall (osi: os_ident) (pa_to_ma: padd -> option madd) (pa: padd) (ma: madd) (p: page),
                 (hypervisor s) osi = Some pa_to_ma
              /\ pa_to_ma pa = Some ma
              /\ (memory s) ma = Some p
              -> page_owned_by p = Os osi.

(* Propiedad 6 *)
(* Todas las page tables de un OS o mapean las direcciones virtuales accesibles a paginas
   pertenecientes a o y las no accesibles a paginas pertenecientes al hypervisor. *)
Definition VSprop6 (s: state) : Prop :=
              forall (osi: os_ident) (ma': madd) (p': page) (va_to_ma: vadd -> option madd) (va: vadd) (ma: madd) (p: page),
                 (memory s) ma' = Some p'
              /\ page_owned_by p' = Os osi
              /\ page_content p' = PT va_to_ma
              -> (os_accessible va /\ va_to_ma va = Some ma /\ (memory s) ma = Some p
                     -> page_owned_by p = Os osi)
              /\ (~os_accessible va /\ va_to_ma va = Some ma /\ (memory s) ma = Some p
                     -> page_owned_by p = Os osi).

(*********************************************************************************)
(* Valid state *)
(* Conjuncion de todas las propiedades anteriores. *)
Definition valid_state (s: state) : Prop :=
              VSprop3 s
           /\ VSprop5 s
           /\ VSprop6 s.

(*********************************************************************************)
(* One-step execution *)
(* La ejecucion de una accion (a) en un estado valido (s) resulta en un nuevo estado (s'). *)
Definition onestepexec (s: state) (a: action) (s': state) : Prop :=
              valid_state s /\ Pre s a /\ Post s a s'.

(*********************************************************************************)
(* Pruebas *)
(* La ejecucion de una accion preserva la validez de la propiedad 3 de valid state. *)
Theorem ActionVerificaVSprop3 : forall (a: action) (s s': state),
           (*VSprop3 s /\*) onestepexec s a s' -> VSprop3 s'.
           (* No hace falta porque esta incluido en onestepexec. *)
Proof.
  unfold VSprop3.
  induction a; intros s s' H H0; destruct H; destruct H; unfold VSprop3 in H; clear H2; destruct H1; clear H1.
    (* read *)
    destruct H2.
    apply H.
    assumption.

    (* write *)
    destruct H2.
    destruct H1.
    clear H1.
    destruct H2.
    clear H1.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    clear H3 x.
    rewrite H1 in *.
    rewrite H2 in *.
    clear H1 H2.
    apply H.
    assumption.

    (* chmod *)
    destruct H2.
      (* trusted_os (active_os s) *)
      destruct H1.
      destruct H2.
      destruct H3.
      assumption.

      (* ~trusted_os (active_os s) *)
      destruct H1.
      destruct H2.
      destruct H3.
      destruct H4.
      clear H H3 H5.
      rewrite H2 in *.
      rewrite H4 in *.
      clear H2 H4.
      destruct H0.
        inversion H.

        contradiction.
Qed.

End ValidState.
