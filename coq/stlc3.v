(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)

(* copied from stlc1.v *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc1.

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
| VFst i => index i h
| VSnd i => match st with
              | (fr,off)::_ =>  if ble_nat off i then index (i - off) fr else None
              | _ => None
            end
end
.

Hint Unfold index_heap.
Hint Unfold index_stack.
Hint Unfold lookup_stack.

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
| heap_const : forall v vheap,
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
(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
 *)
(*Definition heap {X : Type} (env: env_stack X) := fst(env).*)

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

Fixpoint teval_stack(k: nat) (st : stack vl_stack)(env: heap vl_stack)(t: tm)(n: class){struct k}: option (option vl_stack) :=
  match k with
    | 0 => None
    | S k' =>
      match t, n with
        | ttrue, _              => Some (Some (vbool_stack true))
        | tfalse, _             => Some (Some (vbool_stack false))
        | tvar (VFst i), First  => Some (lookup_stack (VFst i) env st)
        | tvar (VSnd i), First  => Some None
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

Inductive equiv_val : stack vl_stack -> vl -> vl_stack -> Prop :=
  | equiv_const : forall b st, equiv_val st (vbool b) (vbool_stack b)
  | equiv_abs : forall H1 H2 idx lS i t n H fr,
                      get_stack_frame lS i = Some (fr, idx) ->
                      equiv_env lS (Def vl H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def vl H1 H2 idx) n t) (vabs_stack H i n t)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def vl H1 (H2++H20) (length H20)) (H1s, (H2s, length H20)) 
.

Print Forall2_ind.
Print equiv_val_ind.
Print equiv_env_ind.


Definition eqv_nested_ind := fun
  (Pv : stack vl_stack -> vl -> vl_stack -> Prop)
  (Pe : stack vl_stack -> venv -> venv_stack -> Prop)
  (fconst : forall (b : bool) (st : stack vl_stack),
       Pv st (vbool b) (vbool_stack b))
  (fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
          (i : st_ptr) (t : tm) (n : class) (H : heap vl_stack)
          (fr : list vl_stack),
        get_stack_frame lS i = Some (fr, idx) ->
        Pe lS (Def vl H1 H2 idx) (H, (fr, idx)) ->
        Pv lS (vabs (Def vl H1 H2 idx) n t) (vabs_stack H i n t))
  (fenv : forall (lS : stack vl_stack) (H1 : list vl) 
         (H1s : list vl_stack) (H2 : list vl) (H2s : list vl_stack)
         (H20 : list vl),
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H1 H1s ->
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H2 H2s ->
       Pe lS (Def vl H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)))
=>
  fix F (s : stack vl_stack) (v : vl) (v0 : vl_stack) (e : equiv_val s v v0): Pv s v v0 :=
match e in (equiv_val s0 v1 v2) return (Pv s0 v1 v2) with
| equiv_const x x0 => fconst x x0
| equiv_abs x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 =>
  fabs x x0 x1 x2 x3 x4 x5 x6 x7 x8 (
         match x9 in (equiv_env s0 v1 v2) return (Pe s0 v1 v2) with
           | eqv_forall x x0 x1 x2 x3 x4 x5 x6 =>
             fenv x x0 x1 x2 x3 x4
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil => Forall2_nil _
                                | Forall2_cons a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x0 x1 x5)
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil => Forall2_nil _
                                | Forall2_cons a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x2 x3 x6)
         end)
end.








Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).

Hint Constructors equiv_env.
Hint Constructors equiv_val.
Hint Constructors equiv_opt.
Hint Constructors equiv_res.

Lemma equiv_length1 : forall H1 H H2 idx fr lS,
   equiv_env lS (Def vl H1 H2 idx) (H, fr) ->
   length H1 = length H.
Proof.
   intros.
   inversion H0; subst.
   induction H8.
     reflexivity.
     simpl. apply eq_S.
     apply IHForall2; eauto.
Qed. 

Lemma index1_equiv : forall H1 H H2 idx fr' lS x,
   equiv_env lS (Def vl H1 H2 idx) (H, fr') ->
   equiv_opt lS (index x H1) (index x H).
Proof.
  intros.
  inversion H0; subst.
  induction H8; eauto.
  simpl.
     replace (length l') with (length l).
     destruct (beq_nat x (length l)); eauto.
  assert (length (x0::l) = length (y::l')); eauto.
  eapply equiv_length1; eauto.
Qed.

Lemma forall2_length : forall A B f l1 l2,
   @Forall2 A B f l1 l2 -> length l1 = length l2.
Proof.
   intros.
   induction H; eauto.
     simpl. apply eq_S. apply IHForall2; eauto.
Qed.

Hint Immediate forall2_length.

Lemma equiv_length2 : forall H l l0 l1 n n0 lS,
  equiv_env lS (Def vl l l0 n) (H, (l1, n0)) ->
  length l0 = n0 + length l1.
Proof.
  intros. 
  inversion H0; subst.
  induction H11.
     simpl. omega.
     simpl. rewrite <- plus_n_Sm. apply eq_S.
     apply IHForall2; eauto.
Qed.

Lemma equiv_idx : forall H l l0 l1 n n0 lS,
  equiv_env lS (Def vl l l0 n) (H, (l1, n0)) ->
  n <= length l0.
Proof.
  intros.
  inversion H0; subst.
  induction H2.
    eauto.
    simpl. rewrite app_length. omega.
Qed.

Lemma index2_equiv : forall H l l0 l1 n n0 lS,
  equiv_env lS (Def vl l l0 n) (H, (l1, n0)) ->
  n = n0 /\ forall i, (n <= i -> equiv_opt lS (index i l0) (index (i - n0) l1)).
Proof.
  intros. 
  inversion H0; subst.
  split.
    - reflexivity.
    - intros. induction H11.
        + simpl. remember (index i H20) as I.
          destruct I; eauto. symmetry in HeqI. eapply index_max in HeqI.
          apply le_not_gt in H1. apply H1 in HeqI. contradiction.
        + simpl. replace (length l') with (length l0).
             case_eq (beq_nat i (length (l0 ++ H20))); intros E.
           * assert (beq_nat (i - length H20) (length l0) = true) as E2.
            { eapply beq_nat_true_iff. eapply equiv_length2 in H0. eapply beq_nat_true_iff in E. 
              rewrite app_length in E. omega. }
              simpl. rewrite E2. eauto.
           * assert (beq_nat (i - length H20) (length l0) = false) as E2.
            { eapply beq_nat_false_iff. eapply equiv_length2 in H0. eapply beq_nat_false_iff in E.
              rewrite app_length in E. omega. }
              simpl. rewrite E2. apply IHForall2; eauto.
           * eapply forall2_length; eauto.
Qed.

Lemma lookup2_equiv : forall env H fr lS i,
   equiv_env (fr::lS) env (H, fr) ->
   equiv_opt (fr::lS) (lookup (VSnd i) env) (lookup_stack (VSnd i) H (fr::lS)).
Proof.
  intros. destruct env. destruct fr. simpl.
  eapply index2_equiv in H0. destruct H0. subst.   
  case_eq (ble_nat n0 i); intros E.
  - eapply H1. eapply ble_nat_true. eauto.
  - eapply e_stuck. 
Qed.

Lemma equiv_sanitize : forall H l l0 l1 n n0 lS,
  equiv_env lS (Def vl l l0 n) (H, (l1, n0)) ->
  equiv_env lS (Def vl l l0 (n + length l1)) (H, ([], n0 + length l1)).
Proof.
  intros.
  inversion H0; subst.
  replace (length l1) with (length H2).
  replace (length H20 + length H2) with (length (H2 ++ H20)).
  replace (H2 ++ H20) with ([] ++ H2 ++ H20).
  constructor;eauto.
  reflexivity.
  rewrite app_length. omega.
  eauto.
Qed.

Hint Unfold get_stack_frame.

Lemma stack_extend_val : forall lS v v' fr,
   equiv_val lS v v' ->
   equiv_val (fr::lS) v v'.
Proof.
  intros. 
  eapply (eqv_nested_ind
            (fun lS v v' => equiv_val (fr::lS) v v')
            (fun lS v v' => equiv_env (fr::lS) v v')).

  - intros. constructor.
  - intros. econstructor. destruct i. simpl. eauto. simpl. eauto. simpl in H3.
    assert (beq_nat n0 (length lS0) = false). admit. (* from index_max *)
    rewrite H5. eauto. eauto.
  - intros. constructor; eauto.
  - eauto.
Qed.

Lemma stack_extend : forall lS env env' fr, 
   equiv_env lS env env' ->
   equiv_env (fr::lS) env env'.
Proof.
  intros.
  inversion H; subst.
    econstructor; eauto.
     Admitted. 

Inductive wf : class -> option (option vl_stack) -> Prop :=
| wf_opt : forall v c, wf_val c v -> wf c (Some (Some v))
.            

Theorem equiv_fc : forall fr lS v v_stack,
  equiv_res (fr::lS) v v_stack -> wf First v_stack -> equiv_res lS v v_stack.
Proof.
  (* idea: if v_stack is first class, it is a bool or a closure without stack frame. *)
  (* it doesn't need a stack frame *)
  intros.
  inversion H0; subst.
  destruct v0; inversion H; subst; inversion H5; subst; inversion H6; subst; clear H; clear H5.
  Case "Bool".
    repeat constructor.
  Case "VAbs".
    repeat constructor. destruct s; try solve by inversion.
    simpl in H11. inversion H11; subst.
    econstructor. simpl. eauto.
    inversion H14. subst. 
    inversion H1. subst. 
    assert (Forall (fun v => wf_val First v) h).
    admit. (* from H4: fc_env h *)
    assert (Forall2 (fun (v : vl) (vs : vl_stack) => equiv_val lS v vs) H2 h).
    admit. (* by induction on H9 *)
    assert (H5 = []). destruct H5. eauto. inversion H15. subst H5. 

    econstructor. eauto. eauto. 
Qed.

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
   destruct v; destruct x; try solve by inversion.
   constructor.
   constructor.
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

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _)) => h
  | _ => []
  end.

Theorem fc_eval : forall k fr lS env_stack t v_stack c,
  teval_stack k (fr::lS) env_stack t c = v_stack ->
  fc_env env_stack -> sc_env (fr::lS) ->
  wf c v_stack.
Proof.
  intros.
  destruct v_stack as [v_stack|].
  destruct v_stack as [v_stack|].
  generalize dependent fr. generalize dependent lS. generalize dependent env_stack0.
  generalize dependent t. generalize dependent v_stack. generalize dependent c.
  induction k; intros.
  Case "k = 0". inversion H.
  Case "k = S k". destruct t;[SCase "True"|SCase "False"|SCase "Var"|SCase "App"|SCase "Abs"]; inversion H; subst.
       
     SCase "True". constructor. constructor.
     SCase "False". constructor. constructor.
   
     - SCase "Var". destruct v; destruct c; try solve by inversion.
       + rewrite H3. constructor. eapply index_fc. eassumption. inversion H3. eauto.
       + rewrite H3. constructor. apply (lookup_snd env_stack0 (fr::lS) (VFst i) v_stack); inversion H3; eauto.
       + rewrite H3. constructor. apply (lookup_snd env_stack0 (fr::lS) (VSnd i) v_stack); inversion H3; eauto.

 
     - SCase "App".
       
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

          inversion FTX; inversion SFX as [a b SFXV]; inversion SFXV; subst.

          eapply IHk with (env_stack0 := (tx_stack :: h)).
            constructor; eauto.
            eapply H3.
            constructor; eauto. constructor. constructor. eauto.
              eapply sc_frame. eapply H1. eauto.
      * SSCase "abs arg is Second".
          rewrite H3. apply fst_any.
          assert (wf Second (Some (Some tx_stack))) as FTX. { eapply IHk; eauto. }
          assert (wf Second (Some (Some (vabs_stack h s Second t)))) as SFX. { eapply IHk; eauto. }

          inversion FTX; inversion SFX as [a b SFXV]; inversion SFXV; subst.

          eapply IHk with (env_stack0 := h); eauto.
            constructor; eauto. constructor.  assumption.
              constructor. eauto.
              eapply sc_frame. eapply H1. eauto.

    - SCase "Abs".
      destruct c.
      * destruct fr. constructor. constructor. eauto.
      * constructor. constructor. eauto.
  - admit.
  - admit.
Qed.       

Theorem teval_equiv : forall k n t env v lS fr env_stack v_stack,
     teval k env t n = v ->
     teval_stack k (fr::lS) env_stack t n = v_stack ->
     
     equiv_env (fr::lS) env (env_stack,fr) ->
     fc_env env_stack -> sc_env (fr::lS) ->
     equiv_res (fr::lS) v v_stack.
Proof.
   intro k. induction k.
   Case "k = 0". intros. inversion H. inversion H0. econstructor.
   Case "k = S k". intros. destruct t;[SCase "True"|SCase "False"|SCase "Var"|SCase "App"|SCase "Abs"]; inversion H; inversion H0.
     
      SCase "True". repeat constructor. 
      SCase "False". repeat constructor. 
    
      - SCase "Var".
        clear H2; clear H3.
        destruct env; destruct v0; destruct n; try solve by inversion; simpl.
        + (* VFst, First *) econstructor. eapply index1_equiv; eauto.
        + (* VFst, Second *) econstructor. eapply index1_equiv; eauto.
        + (* VSnd, First  *) econstructor.
           case_eq (ble_nat (length l0) i); intros E. 
           SSCase "i > length l0".
               remember (index i l0) as HIV.
               destruct HIV. symmetry in HeqHIV. apply index_max in HeqHIV.
               apply ble_nat_true in E. omega.
               constructor. 
           SSCase "i <= length l0".
               constructor.
        + (*VSnd, Second *) econstructor.
               replace (if ble_nat n0 i then index i l0 else None) with (lookup (VSnd i) (Def vl l l0 n0)); eauto.
               replace (let (fr0, off) := fr in if ble_nat off i then index (i - off) fr0 else None) with
                    (lookup_stack (VSnd i) env_stack0 (fr::lS)); eauto.
               eapply lookup2_equiv; eauto.

      - SCase "App". (* case result Some *)
        simpl.
        
        remember (fr::lS) as lS1.
        
        remember (teval k env t1 Second) as tf.
        remember (teval_stack k lS1 env_stack0 t1 Second) as tf_stack.

        assert (equiv_res lS1 tf tf_stack) as EF. subst lS1. eapply IHk; eauto.
        destruct EF. econstructor.
        destruct H6. econstructor. econstructor. 
        destruct H6. econstructor. econstructor.
        
        remember (teval k env t2 n0) as tx.
        remember (teval_stack k lS0 env_stack0 t2 n0) as tx_stack.

        assert (equiv_res lS0 tx tx_stack) as EX. subst lS0. eapply IHk; eauto.

        destruct EX. econstructor.
        destruct H11. econstructor. econstructor.

        rewrite H9. unfold expand_env_stack.
       
        destruct n0. 
        + assert (wf Second (Some (Some (vabs_stack H8 i First t)))). { subst lS0. eapply fc_eval; eauto. }
          assert (wf First (Some (Some  v_stack0))). { subst lS0. eapply fc_eval; eauto. }
          assert (fc_env ((v_stack0 :: H8))). { inversion H12 as [a b H12val]; inversion H13; inversion H12val; subst. constructor; eauto. }
          assert (sc_env ((vabs_stack H8 i First t :: fr0, idx) :: lS0)). 
            { constructor. subst lS0; eauto. constructor. inversion H12; eauto. eapply sc_frame; eauto. }
          eapply equiv_fc;eauto. eapply IHk; eauto. eapply stack_extend. simpl.
          inversion H10; subst idx; subst H7.
          
          eapply (eqv_forall lS0 (v0 ::H6) (v_stack0::H8) (vabs (Def vl H6 (H17 ++ H20) (length H20)) First t :: H17)
                  (vabs_stack H8 i First t :: fr0) H20); eauto.
          
          eapply fc_eval; eauto.
        + assert (wf Second (Some (Some (vabs_stack H8 i Second t)))). { subst lS0. eapply fc_eval; eauto. }
          assert (wf Second (Some (Some  v_stack0))). { subst lS0. eapply fc_eval; eauto. }
          assert (fc_env H8). { inversion H12; subst. inversion H16. eauto. }
          assert (sc_env ((v_stack0 :: vabs_stack H8 i Second t :: fr0, idx) :: lS0)). 
            { constructor. subst lS0; eauto. constructor. inversion H12; eauto. inversion H13; eauto.
              constructor. inversion H12; eauto. eapply sc_frame; eauto. }

          eapply equiv_fc. eapply IHk; eauto. eapply stack_extend.
          inversion H10; subst idx; subst H7. simpl.
          eapply (eqv_forall lS0 H6 H8 (v0 :: vabs (Def vl H6 (H17 ++ H20) (length H20)) Second t :: H17)
                  (v_stack0 :: vabs_stack H8 i Second t :: fr0) H20); eauto.
          eapply fc_eval; eauto. 

      - SCase "Abs".
        simpl.
        destruct n.
        + destruct fr. destruct env. 
          econstructor. econstructor. simpl.
          remember H1 as HX. clear HeqHX.
          eapply index2_equiv in HX. destruct HX. subst. 
          remember H1 as HX. clear HeqHX.
          eapply equiv_length2 in HX. rewrite HX. 
          eapply equiv_abs. simpl. eauto.
          eapply equiv_sanitize. eauto.
        + simpl. destruct fr. destruct env. econstructor. econstructor.
          remember H1 as HX. clear HeqHX.
          eapply index2_equiv in HX. destruct HX. subst. 
          eapply equiv_abs. simpl.
          assert (beq_nat (length lS) (length lS) = true) as A. eapply beq_nat_true_iff. eauto. rewrite A. eauto. eauto. 
Qed.
