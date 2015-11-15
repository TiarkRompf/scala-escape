(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)

(* copied from stlc1.v *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.


Inductive class : Type :=
  | First : class
  | Second : class
.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> class -> ty -> ty
.

Inductive var : Type :=
  | VFst  : id -> var
  | VSnd  : id -> var
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  (*| tvar : var -> tm*) 
  | tvar : var -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : class -> tm -> tm (* \f x.y *)
.

Inductive env (X: Type) :=
  | Def : list X -> list X -> nat -> env X.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : env vl -> class -> tm -> vl
.

Definition venv := env vl.
Definition tenv := env ty.

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Definition lookup {X : Type} (n : var) (l : env X) : option X :=
  match l with
    | Def l1 l2 m =>
         match n with
           | VFst idx => index idx l1
           | VSnd idx => if ble_nat idx m then None else index idx l2
         end
   end
.

Definition sanitize_env {X : Type} (c : class) (l : env X) : env X :=
   match c with
   | First => match l with
                 | Def l1 l2 _ => Def X l1 l2 (length l2)
                 end
   | Second => l
end
.

Definition expand_env {X : Type} (l : env X) (x : X) (c : class) : (env X) :=
match l with
| Def l1 l2 m =>
   match c with
   | First => Def X (x::l1) l2 m
   | Second => Def X l1 (x::l2) m
   end
end
.

Inductive has_type : tenv -> tm -> class -> ty -> Prop :=
| t_true: forall n env,
           has_type env ttrue n TBool
| t_false: forall n env,
           has_type env tfalse n TBool
| t_var: forall n x env T1,
           lookup x (sanitize_env n env) = Some T1 ->
           has_type env (tvar x) n T1
| t_app: forall m n env f x T1 T2,
           has_type env f Second (TFun T1 m T2) ->
           has_type env x m T1 ->
           has_type env (tapp f x) n T2
| t_abs: forall m n env y T1 T2,
           has_type (expand_env (sanitize_env n env) T1 m) y First T2 ->
           has_type env (tabs m y) n (TFun T1 m T2)
.

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env (Def vl nil nil O) (Def ty nil nil O) 
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv y T1 T2 m,
    wf_env venv tenv ->
    has_type (expand_env tenv T1 m) y m T2 ->
    val_type env (vabs venv m y) (TFun T1 m T2)
.

Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.



(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
 *)

Fixpoint teval(k: nat)(env: venv)(t: tm)(n: class){struct k}: option (option vl) :=
  match k with
    | 0 => None
    | S k' =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (lookup x (sanitize_env n env))
        | tabs m y   => Some (Some (vabs (sanitize_env n env) m y))
        | tapp ef ex   =>
           match teval k' env ef Second with
             | None => None
             | Some None => Some None
             | Some (Some (vbool _)) => Some None
             | Some (Some (vabs env2 m ey)) =>
                match teval k' env ex m with
                  | None => None
                  | Some None => Some None
                  | Some (Some vx) =>
                       teval k' (expand_env env2 vx m) ey First
                end
          end
      end
  end.


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
  intros. destruct env0; destruct n; inversion H; auto.
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

End STLC.