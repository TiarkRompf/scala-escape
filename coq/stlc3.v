(* ############################################################ *)
(*                                                              *)
(*        Semantic equivalence of STLC 1/2 and STLCs 1/2        *)
(*                                                              *)
(* ############################################################ *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc1.
Require Export stlc2.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### semantic equivalence ### *)

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

(* Since equiv_env uses equiv_val indirectly through Forall2,
   Coq's auto-generated induction principles are not strong enough.
   Hence, we define our own nested induction principle *)

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

(* lift equivalence to timeout and error results *)
Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

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
   equiv_opt (fr::lS) (lookup (V Second i) env) (lookup_stack (V Second i) H (fr::lS)).
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
    assert (beq_nat n0 (length lS0) = false).
     { apply index_max in H3. apply beq_nat_false_iff. intro contra. subst. eapply lt_irrefl. eauto. }
    rewrite H5. eauto. eauto.
  - intros. constructor; eauto.
  - eauto.
Qed.

Lemma stack_extend : forall lS env env' fr, 
   equiv_env lS env env' ->
   equiv_env (fr::lS) env env'.
Proof.
  intros. inversion H; subst.
  econstructor.
  - induction H0; econstructor. apply stack_extend_val; eauto. eauto.
  - induction H3; econstructor. apply stack_extend_val; eauto. eauto.
Qed.


Lemma fc_env_wf: forall H,
  fc_env H -> (Forall (fun v => wf_val First v) H).
Proof.
  intros. induction H0. eauto. eauto. 
Qed.

Lemma equiv_val_fc : forall lS v v_stack fr,
  equiv_val (fr::lS) v v_stack -> wf_val First v_stack -> equiv_val lS v v_stack.
Proof.
  (* idea: if v_stack is first class, it is a bool or a closure without stack frame. *)
  (* it doesn't need a stack frame *)
  intros.
  eapply (eqv_nested_ind
            (fun lS1 v v_stack =>
               lS1 = fr::lS ->
               equiv_val (fr::lS) v v_stack ->
               wf_val First v_stack ->
               equiv_val lS v v_stack)
            (fun lS1 v v_stack =>
               lS1 = fr::lS ->
               equiv_env (fr::lS) v v_stack ->
               fc_env (fst v_stack) -> (fst (snd v_stack)) = [] ->
               equiv_env lS v v_stack)) with (s:=fr::lS);
    intros; try subst lS0.
  - Case "Bool".
    constructor.
  - Case "VAbs".
    inversion H8. subst. 
    econstructor; eauto.
    inversion H4. subst.
    inversion H7. subst.
    inversion H15. subst.
    eapply H5; eauto. 
  - Case "env".
    simpl in H7. simpl in H8. subst. eapply fc_env_wf in H7.
    inversion H4. subst. inversion H6. inversion H16. subst. 
    constructor.
    + clear H6. 
      induction H12.
      * eauto.
      * inversion H3. inversion H7. subst. 
        constructor. eapply H9; eauto. eauto. 
    + eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto. 
Qed.
    
Lemma equiv_fc : forall fr lS v v_stack,
  equiv_res (fr::lS) v v_stack -> wf First v_stack -> equiv_res lS v v_stack.
Proof.
  intros.
  inversion H; subst. eauto. constructor.
  inversion H1; subst. eauto. constructor.
  inversion H0. 
  eapply equiv_val_fc; eauto. 
Qed.  

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _)) => h
  | _ => []
  end.


(* ### Theorem 3.3 ### *)
(* semantic equivalence of STLC 1/2 and STLCs 1.2 *)

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
        destruct env; destruct v0; destruct n; destruct c; try solve by inversion; simpl.
        + (* VFst, First *) econstructor. eapply index1_equiv; eauto.
        + (* VSnd, First  *) econstructor.
           case_eq (ble_nat (length l0) i); intros E. 
           SSCase "i > length l0".
               remember (index i l0) as HIV.
               destruct HIV. symmetry in HeqHIV. apply index_max in HeqHIV.
               apply ble_nat_true in E. omega.
               constructor. 
           SSCase "i <= length l0".
               constructor.
        + (* VFst, Second *) econstructor. eapply index1_equiv; eauto.
        + (*VSnd, Second *) econstructor.
               replace (if ble_nat n0 i then index i l0 else None) with (lookup (V Second i) (Def vl l l0 n0)); eauto.
               replace (let (fr0, off) := fr in if ble_nat off i then index (i - off) fr0 else None) with
                    (lookup_stack (V Second i) env_stack (fr::lS)); eauto.
               eapply lookup2_equiv; eauto.

      - SCase "App". (* case result Some *)
        simpl.
        
        remember (fr::lS) as lS1.
        
        remember (teval k env t1 Second) as tf.
        remember (teval_stack k lS1 env_stack t1 Second) as tf_stack.

        assert (equiv_res lS1 tf tf_stack) as EF. subst lS1. eapply IHk; eauto.
        destruct EF. econstructor.
        destruct H6. econstructor. econstructor. 
        destruct H6. econstructor. econstructor.
        
        remember (teval k env t2 n0) as tx.
        remember (teval_stack k lS0 env_stack t2 n0) as tx_stack.

        assert (equiv_res lS0 tx tx_stack) as EX. subst lS0. eapply IHk; eauto.

        destruct EX. econstructor.
        destruct H11. econstructor. econstructor.

        rewrite H9. unfold expand_env_stack.
       
        destruct n0. 
        + assert (wf Second (Some (Some (vabs_stack H8 i First t)))). { subst lS0. eapply fc_eval; eauto. }
          assert (wf First (Some (Some  v_stack0))). { subst lS0. eapply fc_eval; eauto. }
          assert (fc_env ((v_stack0 :: H8))). { inversion H12 as [a b H12val| |]; inversion H13; inversion H12val; subst. constructor; eauto. }
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
