(*******************************************************************
 * Este archivo especifica las propiedades de isolation.
 ******************************************************************)

Require Export ValidState.

Section Isolation.

(* Read Isolation *)
(* Ningun OS puede leer memoria que no le corresponde. *)
Lemma ReadIsolation : forall (s s': state) (va: vadd),
         onestepexec s (read va) s' ->
            exists (ma: madd), va_mapped_to_ma s va ma
         /\ exists (pg: page), Some pg = (memory s) ma
         /\ page_owned_by pg = Os (active_os s).
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H1.
  destruct H0.
  clear H3.
  destruct H0.
  destruct H3.
  destruct H4.
  rename x into ma.
  destruct H4.
  destruct H5.
  rename x into pg.
  destruct H5.
  clear H6.
  exists ma.
  split.
    assumption.

    exists pg.
    split.
      assumption.

      clear H H3.
      destruct H4.
      rename x into o.
      destruct H.
      destruct H3.
      rename x into pa_to_ma.
      destruct H3.
      destruct H4.
      rename x into ma'.
      destruct H4.
      destruct H6.
      rename x into p.
      destruct H6.
      destruct H7.
      rename x into va_to_ma.
      destruct H7.
      elim (H2 (active_os s) ma' p va_to_ma va ma pg); clear H2.
        intros.
        clear H9.
        apply H2.
        clear H2.
        split.
          assumption.

          split.
            assumption.

            symmetry.
            assumption.

        split.
          symmetry.
          assumption.

          split.
            apply (H1 (active_os s) pa_to_ma (curr_page o) ma' p).
            repeat split; symmetry; assumption.

            symmetry.
            assumption.
Qed.

End Isolation.
