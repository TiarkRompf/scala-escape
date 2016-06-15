(* ############################################################ *)
(*                                                              *)
(*             STLCs 1/2 and its lifetime properties            *)
(*                                                              *)
(* ############################################################ *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc1.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Stacks, stack-frames, closures, etc ### *)

(* To distinguish from the types in stlc1, we frequently use
   a xx_stack suffix:
      - env     ~  env_stack
      - vl      ~  vl_stack
      - lookup  ~  lookup_stack
   we define formal equivalence relations in file stlc3.v *)

Definition stack_frame (X : Type) := prod (list X) nat.
Definition stack (X : Type) := list (stack_frame X).
Definition heap (X : Type) := list X.
Definition env_stack (X : Type) := prod (heap X) (stack_frame X).

(* Stack pointer type.
     - S0 means that there is no stack pointer (fst class closure)
     - Si keeps the index of the stack pointer
*)
Inductive st_ptr : Type :=
| S0 : nat -> st_ptr
| Si : nat -> st_ptr
.

(* STLCs 1/2 values *)
Inductive vl_stack : Type :=
| vbool_stack : bool -> vl_stack
| vabs_stack  : heap vl_stack -> st_ptr -> class -> tm -> vl_stack
.

Definition venv_stack := env_stack vl_stack.

Hint Unfold venv_stack.

Definition index_heap {X : Type} (n : id) (l : env_stack X) : option X := index n (fst l).
Definition index_stack {X : Type} (n : id) (l : env_stack X) : option X :=
match l with
| (_, ([], _))          => None
| (_, (h, off)) => if ble_nat off n then index (n - off) h else None
end.

Definition lookup_stack {X : Type} (n : var) (h: heap X) (st : stack X) : option X :=
match n with
| V First i => index i h
| V Second i => match st with
              | (fr,off)::_ =>  if ble_nat off i then index (i - off) fr else None
              | _ => None
            end
end
.

Hint Unfold index_heap.
Hint Unfold index_stack.
Hint Unfold lookup_stack.

Definition expand_env_stack {X : Type} (env : env_stack X) (x : X) (n : class) :=
match env, n with
| (h, (l,off)), First  => (x::h, (l,off))
| (h, (l,off)), Second =>  (h, (x::l, off))
end
.

Definition get_stack_frame {X : Type} (st : stack X) (ptr: st_ptr) :=
  match ptr with
    | S0 idx => Some (nil, idx)
    | Si idx =>  index idx st (*match index idx st with
                     | None => Some (nil,0)
                     | Some s => Some s
                   end *)
end.

(* ### Well-Formedness ### *)

(* well-formedness for `proper` 1st/2nd class values: *)
(* 1st-class closures may not have 2nd class references *)
Inductive wf_val : class -> vl_stack -> Prop :=
| wf_val_const : forall bool c, wf_val c (vbool_stack bool)
| wf_val_closureF : forall tm vheap class idx,
      fc_env vheap ->
      wf_val First (vabs_stack vheap (S0 idx) class tm)
| wf_val_closureS : forall tm vheap class i,
      fc_env vheap ->
      wf_val Second (vabs_stack vheap i class tm)
with fc_env : heap vl_stack -> Prop := (* H, x^1 :v *)
| heap_nil : fc_env []
| heap_cons : forall v vheap,
     wf_val First v ->
     fc_env vheap ->
     fc_env (v::vheap)
with sc_env : stack vl_stack -> Prop :=
| stack_nil : sc_env []
| stack_cons : forall vstack fr idx,
     sc_env vstack ->
     Forall(fun v => wf_val Second v) fr ->
     sc_env ((fr, idx)::vstack)
.

(* lift wf_val to timeouts and errors *)
Inductive wf : class -> option (option vl_stack) -> Prop :=
| wf_opt : forall v c, wf_val c v -> wf c (Some (Some v))
| wf_timeout: forall c, wf c None
| wf_stuck: forall c, wf c (Some None)
.            

Definition fc_val v := wf_val First v.


(* ### Operational Semantics ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval_stack(k: nat) (st : stack vl_stack)(env: heap vl_stack)(t: tm)(n: class){struct k}: option (option vl_stack) :=
  match k with
    | 0 => None
    | S k' =>
      match t, n with
        | ttrue, _              => Some (Some (vbool_stack true))
        | tfalse, _             => Some (Some (vbool_stack false))
        | tvar (V First i),  First  => Some (lookup_stack (V First i) env st)
        | tvar (V Second i), First  => Some None
        | tvar i, Second        => Some (lookup_stack i env st)
        | tabs m y, First       => (* Some (Some (vabs_stack env (S0 0) m y)) *)
                                   match st with
                                   | [] => Some None
                                   | (fr, idx)::_ => Some (Some (vabs_stack env (S0 (idx + length fr)) m y))
                                   end
        | tabs m y, Second      => match st with
                                     | [] => Some None
                                     | _::st1 => 
                                       Some (Some (vabs_stack env (Si (length st1)) m y))
                                   end
        | tapp ef ex, _   =>
           match teval_stack k' st env ef Second with
             | None => None
             | Some None => Some None
             | Some (Some (vbool_stack _)) => Some None
             | Some (Some (vabs_stack env2 i m ey)) =>
                match teval_stack k' st env ex m with
                  | None => None
                  | Some None => Some None
                  | Some (Some vx) =>
                    match get_stack_frame st i with
                      | None => Some None
                      | Some fr =>
                        let (env',fr') := expand_env_stack (expand_env_stack (env2,fr) (vabs_stack env2 i m ey) Second) vx m in
                        teval_stack k' (fr'::st) env' ey First
                    end
                end
          end
      end
  end.


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

Lemma index_fc: forall H x v,
   fc_env H ->
   index x H = Some v ->
   wf_val First v.
Proof.
   intros.
   induction H0.
     inversion H1.
     case_eq (beq_nat x (length vheap)); intros E; simpl in H1.
     + rewrite E in H1. inversion H1; subst. eauto.
     + rewrite E in H1. eauto.
Qed.

Lemma lookup_snd : forall H lS x v,
   fc_env H -> sc_env lS ->
   lookup_stack x H lS = Some v ->
   wf_val Second v.
Proof.
   intros.
   destruct v.
   destruct x; destruct c; try solve by inversion.
   constructor. constructor.
   destruct x. destruct c0. try solve by inversion. 
   constructor. assert (wf_val First (vabs_stack h s c t)). eapply index_fc; eauto.
   inversion H3; eauto.
   induction H1.
      - inversion H2. 
      - case_eq (ble_nat idx i); intros E; simpl in H2.
        + rewrite E in H2. induction H3. inversion H2. 
        case_eq (beq_nat (i - idx) (length l)); intros E2; simpl in H2.
          * rewrite E2 in H2. inversion H2; subst; eauto. 
          * rewrite E2 in H2. apply IHForall. simpl. eauto.
        + rewrite E in H2. inversion H2.
Qed.

Lemma fst_any : forall v c,
  wf First v -> wf c v.
Proof.
  intros.
  destruct c; eauto.
  repeat (destruct v as [v|]; try solve by inversion); repeat constructor.
  inversion H; subst.
  inversion H2; eauto.
Qed.

Lemma sc_frame : forall fr idx lS i,
  sc_env lS ->
  get_stack_frame lS i = Some (fr, idx) ->
  Forall(fun v => wf_val Second v) fr.
Proof.
  intros fr idx lS i H.
  generalize dependent fr. generalize dependent i.
  induction H; intros.
  - destruct i; inversion H. constructor.
  - destruct i; inversion H1; subst.
     + constructor.
     + case_eq (beq_nat n (length vstack)); intros E.
       * rewrite E in H3. inversion H3; subst. assumption.
       * rewrite E in H3. apply IHsc_env with (i := Si n). simpl. assumption.
Qed.


(* ### Theorem 3.2 ### *)
(* evaluation in STLCs 1/2 never leaks stack references *)

Theorem fc_eval : forall k fr lS env_stack t v_stack c,
  teval_stack k (fr::lS) env_stack t c = v_stack ->
  fc_env env_stack -> sc_env (fr::lS) ->
  wf c v_stack.
Proof.
  intros.
  destruct v_stack as [v_stack|];[destruct v_stack as [v_stack|]|].
  - generalize dependent fr. generalize dependent lS. generalize dependent env_stack0.
  generalize dependent t. generalize dependent v_stack. generalize dependent c.
  induction k; intros.
  Case "k = 0". inversion H.
  Case "k = S k". destruct t;[SCase "True"|SCase "False"|SCase "Var"|SCase "App"|SCase "Abs"]; inversion H; subst.
       
     SCase "True". constructor. constructor.
     SCase "False". constructor. constructor.
   
     + SCase "Var". destruct v; destruct c0; destruct c; try solve by inversion.
       * rewrite H3. constructor. eapply index_fc. eassumption. inversion H3. eauto.
       * rewrite H3. constructor. apply (lookup_snd env_stack0 (fr::lS) (V First i) v_stack); inversion H3; eauto.
       * rewrite H3. constructor. apply (lookup_snd env_stack0 (fr::lS) (V Second i) v_stack); inversion H3; eauto.

 
     + SCase "App".
       
       remember (teval_stack k (fr::lS) env_stack0 t1 Second) as tf_stack.

       destruct tf_stack as [tf_stack|]; try solve by inversion.
       destruct tf_stack as [tf_stack|]; try solve by inversion.
       destruct tf_stack; try solve by inversion.
 
       remember (teval_stack k (fr::lS) env_stack0 t2 c0) as tx_stack.
       
       destruct tx_stack as [tx_stack|]; try solve by inversion.
       destruct tx_stack as [tx_stack|]; try solve by inversion.

       remember (get_stack_frame (fr::lS) s) as frame.
       
       destruct frame; try solve by inversion. destruct p.

       destruct c0; simpl in H3; simpl.
       * SSCase "abs arg is First".
          rewrite H3. apply fst_any. 
          assert (wf First (Some (Some tx_stack))) as FTX. { eapply IHk; eauto. }
          assert (wf Second (Some (Some (vabs_stack h s First t)))) as SFX. { eapply IHk; eauto. }

          inversion FTX; inversion SFX as [a b SFXV| |]; inversion SFXV; subst.

          eapply IHk with (env_stack0 := (tx_stack :: h)).
            constructor; eauto.
            eapply H3.
            constructor; eauto. constructor. constructor. eauto.
              eapply sc_frame. eapply H1. eauto.
      * SSCase "abs arg is Second".
          rewrite H3. apply fst_any.
          assert (wf Second (Some (Some tx_stack))) as FTX. { eapply IHk; eauto. }
          assert (wf Second (Some (Some (vabs_stack h s Second t)))) as SFX. { eapply IHk; eauto. }

          inversion FTX; inversion SFX as [a b SFXV| |]; inversion SFXV; subst.

          eapply IHk with (env_stack0 := h); eauto.
            constructor; eauto. constructor.  assumption.
              constructor. eauto.
              eapply sc_frame. eapply H1. eauto.

    + SCase "Abs".
      destruct c.
      * destruct fr. constructor. constructor. eauto.
      * constructor. constructor. eauto.
  - constructor.
  - constructor.
Qed.
