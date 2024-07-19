(*******************************************************************
 * Este archivo especifica el estado.
 ******************************************************************)

Section State.

(* Identificadores de OSs e Hypercalls *)
Parameter os_ident: Set.
Parameter os_ident_eq: forall (oi1 oi2: os_ident), {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyper_call: Set.

(*********************************************************************************)
(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq: forall (va1 va2: vadd), {va1 = va2} + {va1 <> va2}.

(* Direcciones de Maquina. *)
Parameter madd: Set.
Parameter madd_eq: forall (ma1 ma2: madd), {ma1 = ma2} + {ma1 <> ma2}.

(* Direcciones Fisicas : 
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoria
contigua. Estos no ven direcciones de maquina. *)
Parameter padd: Set.
Parameter padd_eq: forall (pa1 pa2: padd), {pa1 = pa2} + {pa1 <> pa2}.

(* Memory values. *)
Parameter value: Set.
Parameter value_eq: forall (val1 val2: value), {val1 = val2} + {val1 <> val2}.

(*********************************************************************************)
(* Environment *)
Record context : Set :=
       Context { ctxt_vadd_accessible : vadd -> bool;    (* una direccion virtual es accesible, i.e.
                                                            no esta reserveda por el Hypervisor *)
                 ctxt_oss             : os_ident -> bool (* guest Oss (Confiable / No Confiable) *)
               }.

Parameter ctxt : context.

(* El predicado os_accessible(va) es verdadero cuando va pertenece al conjunto de direcciones
virtuales accesibles por algun OS. *)
Definition os_accessible (va: vadd) : Prop :=
              ctxt_vadd_accessible ctxt va = true.

(* El predicado trusted_os indica si un OS es confiable o no. *)
Definition trusted_os (osi: os_ident) : Prop :=
              ctxt_oss ctxt osi = true.

(*********************************************************************************)
(* Operating systems *)
Record os : Set :=
       { curr_page : padd;
         hcall     : option Hyper_call
       }.

Definition oss_map := os_ident -> option os.

(*********************************************************************************)
(* Execution modes *)
Inductive exec_mode : Set :=
          | usr : exec_mode
          | svc : exec_mode.

Inductive os_activity : Set :=
          | running : os_activity
          | waiting : os_activity.

(*********************************************************************************)
(* Memory mappings *)
Definition hypervisor_map := os_ident -> option (padd -> option madd).

Inductive content : Set :=
          | RW (v: option value)               : content
          | PT (va_to_ma: vadd -> option madd) : content
          | Other                              : content.

Inductive page_owner : Set :=
          | Hyp                : page_owner
          | Os (osi: os_ident) : page_owner
          | No_Owner           : page_owner.

Record page : Set :=
       { page_content  : content;
         page_owned_by : page_owner
       }.

Definition system_memory := madd -> option page.

(*********************************************************************************)
(* States *)
Record state : Set :=
       { active_os     : os_ident;
         aos_exec_mode : exec_mode;
         aos_activity  : os_activity;
         oss           : oss_map;
         hypervisor    : hypervisor_map;
         memory        : system_memory
       }.

(*********************************************************************************)
(* Relacion s ~_{memory,ma} s' *)
(* s y s' difieren a lo sumo en el valor asociado al indice ma del componente memoria. *)
Definition differ_at_most_memory (s s': state) (ma: madd) : Prop :=
              active_os s = active_os s'
           /\ aos_exec_mode s = aos_exec_mode s'
           /\ aos_activity s = aos_activity s'
           /\ oss s = oss s'
           /\ hypervisor s = hypervisor s'
           /\ forall (m: madd), m <> ma -> (memory s) m = (memory s') m.

(*********************************************************************************)
(* Relacion va_mapped_to_ma *)
Definition va_mapped_to_ma (s: state) (va: vadd) (ma: madd) : Prop :=
              exists (o: os), Some o = (oss s) (active_os s)
           /\ exists (pa_to_ma: padd -> option madd), Some pa_to_ma = (hypervisor s) (active_os s)
           /\ exists (ma': madd), Some ma' = pa_to_ma (curr_page o)
           /\ exists (p: page), Some p = (memory s) ma'
           /\ exists (va_to_ma: vadd -> option madd), PT va_to_ma = page_content p
           /\ va_to_ma va = Some ma.

End State.
