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

Inductive fc_val : vl_stack -> Prop :=
| fc_val_const : forall bool, fc_val (vbool_stack bool)
| fc_val_closure : forall tm vheap class idx,
      fc_env vheap ->
      fc_val (vabs_stack vheap (S0 idx) class tm)

with fc_env : heap vl_stack -> Prop := (* H, x^1 :v *)
| heap_nil : fc_env []
| heap_const : forall v vheap,
     fc_val v ->
     fc_env vheap ->
     fc_env (v::vheap).

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
  | equiv_const : forall b b' st, b = b' -> equiv_val st (vbool b) (vbool_stack b')
  | equiv_abs : forall H1 H2 idx H lS i t n fr,
                      get_stack_frame lS i = Some (fr ,idx) ->
                      equiv_env lS (Def vl H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def vl H1 H2 idx) n t) (vabs_stack H i n t)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def vl H1 (H2++H20) (length H20)) (H1s, (H2s, length H20)) 
.


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
   Admitted.

Lemma stack_extend : forall lS env env' fr, 
   equiv_env lS env env' ->
   equiv_env (fr::lS) env env'.
Proof.
  intros.
  inversion H; subst.
    econstructor; eauto.
     Admitted. 

Inductive fc : option (option vl_stack) -> Prop :=
| fc_opt : forall v, fc_val v -> fc (Some (Some v))
.            

Theorem equiv_fc : forall fr lS v v_stack,
  equiv_res (fr::lS) v v_stack -> fc v_stack -> equiv_res lS v v_stack.
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


Theorem fc_eval : forall k fr lS env_stack t v_stack,
  teval_stack k (fr::lS) env_stack t First = v_stack ->
  fc v_stack.
Proof.
admit.
Qed.

Theorem teval_equiv : forall k n t env v lS fr env_stack v_stack,
     teval k env t n = v ->
     teval_stack k (fr::lS) env_stack t n = v_stack ->
     
     equiv_env (fr::lS) env (env_stack,fr) ->
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
        destruct H4. econstructor. econstructor. 
        destruct H4. econstructor. econstructor.
        
        remember (teval k env t2 n0) as tx.
        remember (teval_stack k lS0 env_stack0 t2 n0) as tx_stack.

        assert (equiv_res lS0 tx tx_stack) as EX. subst lS0. eapply IHk; eauto.

        destruct EX. econstructor.
        destruct H9. econstructor. econstructor.

        rewrite H7. unfold expand_env_stack.
       
        destruct n0. 
        + eapply equiv_fc. eapply IHk. eauto. eauto. eapply stack_extend. simpl.
          inversion H8; subst idx; subst H5.
          eapply (eqv_forall lS0 (v0 ::H4) (v_stack0::H6) (vabs (Def vl H4 (H11 ++ H20) (length H20)) First t :: H11)
                  (vabs_stack H6 i First t :: fr0) H20); eauto.
          eapply fc_eval. eauto.
        + eapply equiv_fc. eapply IHk. eauto. eauto. eapply stack_extend.
          inversion H8; subst idx; subst H5. simpl.
          eapply (eqv_forall lS0 H4 H6 (v0 :: vabs (Def vl H4 (H11 ++ H20) (length H20)) Second t :: H11)
                  (v_stack0 :: vabs_stack H6 i Second t :: fr0) H20); eauto.
          eapply fc_eval. eauto. 

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


(* TODO: 

Theorem: The lifetimes of second-class values follow a stack discipline.

We define a lower-level operational
semantics that splits environments into first-class and second-class parts,
and maintains a stack of second-class environments through all
function calls. Closures will contain a first-class environment but
only a stack pointer to represent the second-class part. When invoking
a closure, the stack pointer will be used to find the correct caller
environment in which to resolve the callee's free second-class variables.
Proving equivalence of the high-level and low-level semantics will
establish this proposition.

Tentative rules:

N,M ::= nat
H,S ::= 0 | H,x:v


H S_0,..,S_N |- c ⇓^n c    CST

x^m:v  in  H S_N^[<=n]
-----------------------    VAR
H S0,..,SN |- x^m ⇓^n v

H S0,..,SN |- λx^m.t ⇓^n  <H N, λx^m.t>    ABS

H S0,..,SM,..,SN |- t1 ⇓^2  <H' M, λx^m.t3>
H S0,..,SM,..,SN |- t2 ⇓^m  v2
H S0,..,SM,..,SN,(SM x^m: v2) |- t3 ⇓^1  v3
-------------------------------------------    APP
H S0,..,SM,..,SN |- t1 t2 ⇓^n v3


We want to prove that this semantics is equivalent to teval above.

How to do this we need to define alternative version (_stack) of
the following:

  Inductive vl_stack : Type      (because closures are different here)

  Definition venv_stack          (this will be a pair (list vl) * (list list vl),
                                  the H S0,..,SN above)

  Fixpoint teval_stack(k: nat)(env: venv_stack)(t: tm)(n: class){struct k}: option (option vl_stack) :=

And then have correspondences that relate vl/vl_stack, venv/venv_stack, etc.
Let's call these corr_vl, corr_venv, ... .

The final theorem we want to prove is:

  Theorem eval_equiv : forall n e c G GS v vS,
    corr_venv G GS ->
    teval n G e c = v -> 
    teval_stack n GS c = vS ->
    corr_vl v vS.

So, given corresponding environments, the two eval functions produce a
corresponding result.

*)






Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.

Hint Constructors option.
Hint Constructors list.
Hint Constructors env.

Hint Unfold index.
Hint Unfold length.
Hint Unfold expand_env.

Hint Resolve ex_intro.

Definition length_env {X : Type} (c : class) (env : env X): nat :=
match env, c with
| Def l1 l2 n, First => length l1
| Def l1 l2 n, Second => length l2
end
.

Hint Unfold expand_env.

Lemma length_env_incr : forall (X : Type) n m env (x : X),
   n = m ->
   length_env n (expand_env env x m) = 1 + length_env n env.
Proof.
  intros. destruct env; destruct n; inversion H; auto.
Qed.
   
Lemma length_env_same : forall (X : Type) n m env (x : X),
   n <> m ->
   length_env n (expand_env env x m) = length_env n env.
Proof.
  intros. destruct env0; destruct n; destruct m.
      apply ex_falso_quodlibet; auto.
      auto.
      auto.
      apply ex_falso_quodlibet; auto.
Qed.

Hint Rewrite length_env_incr.
Hint Rewrite length_env_same.
Hint Unfold not.

Lemma wf_length : forall vs ts,
      wf_env vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H. auto.
  destruct IHwf_env.
  destruct n. 
  Case "First"; split.
  repeat rewrite length_env_incr; auto.
  repeat rewrite length_env_same; auto.
  unfold not; intros. inversion H3. unfold not; intros. inversion H3.
  Case "Second"; split.
  repeat rewrite length_env_same; auto.
  unfold not; intros. inversion H3. unfold not; intros. inversion H3.
  repeat rewrite length_env_incr; auto.
Qed.

Hint Immediate wf_length.

Definition get_class (x : var): class :=
match x with
| VFst _ => First
| VSnd _ => Second
end
.

Definition get_idx (x : var): nat :=
match x with
| VFst n => n
| VSnd n => n
end
.

Lemma index_max : forall X vs x (T: X),
                       lookup x vs = Some T ->
                       get_idx x < length_env (get_class x) vs.
Proof.
  intros X vs; destruct vs as [l1 l2 n].
  intros x T H.
  destruct x; simpl.
  Case "VFst"; induction l1.
    SCase "nil". intros. inversion H.
    SCase "cons".
       intros. inversion H.
       case_eq (beq_nat i (length l1)); intros E.
       SSCase "hit".
          rewrite E in H1. inversion H1. subst.
          eapply beq_nat_true in E. 
          unfold length. unfold length in E. rewrite E. eauto.
       SSCase "miss".
          rewrite E in H1.
          assert (i < length l1). eapply IHl1. apply H1.
          compute. eauto.
  Case "VSnd"; induction l2.
    SCase "nil". inversion H. destruct (ble_nat i n); inversion H1.
    SCase "cons". intros. inversion H.
       case_eq (beq_nat i (length l2)); intros E.
       SSCase "hit".
          rewrite E in H1. inversion H1. subst.
          eapply beq_nat_true in E. 
          unfold length. unfold length in E. rewrite E. eauto.
       SSCase "miss".
          rewrite E in H1.
          assert (i < length l2). eapply IHl2. apply H1.
          compute. eauto.
Qed.

Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof. intros. induction H; eauto. Qed.

Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
       Case "nil". inversion H0.
       Case "cons". inversion H0.
         case_eq (beq_nat i (length ts)).
           SCase "hit".
             intros E.
             rewrite E in H3. inversion H3. subst t.
             assert (beq_nat i (length vs) = true). eauto.
             assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.

  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; inversion H0; subst T2; subst; eauto.
Qed.


Lemma invert_abs: forall venv vf vx T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv y T3 T4,
    vf = (vabs env y) /\ 
    wf_env env tenv /\
    has_type (T3::(TFun T3 T4)::tenv) y T4 /\
    stp venv T1 (vx::vf::env) T3 /\
    stp (vx::vf::env) T4 venv T2.
Proof.
  intros. inversion H. repeat eexists; repeat eauto.
Qed.


(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0.
  
  Case "True".  eapply not_stuck. eapply v_bool.
  Case "False". eapply not_stuck. eapply v_bool.

  Case "Var".
    destruct (index_safe_ex venv0 tenv0 T i) as [v [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply V.

  Case "App".
    remember (teval n venv0 e1) as tf.
    remember (teval n venv0 e2) as tx. 
    subst T.
    
    destruct tx as [rx|]; try solve by inversion.
    assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
    inversion HRX as [? vx]. 

    destruct tf as [rf|]; subst rx; try solve by inversion.  
    assert (res_type venv0 rf (TFun T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
    inversion HRF as [? vf].

    destruct (invert_abs venv0 vf vx T1 T2) as
        [env1 [tenv [y0 [T3 [T4 [EF [WF [HTY [STX STY]]]]]]]]]. eauto.
    (* now we know it's a closure, and we have has_type evidence *)

    assert (res_type (vx::vf::env1) res T4) as HRY.
      SCase "HRY".
        subst. eapply IHn. eauto. eauto.
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto.
        (* wf_env f   *) econstructor. eapply v_abs; eauto.
        eauto.

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.
    
  Case "Abs". intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs; eauto.
Qed.

End STLC2.