From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Import ListNotations.

Parameter security_group : Type.
Parameter sg_le : security_group -> security_group -> Prop.
Parameter sg_join : security_group -> security_group -> security_group.

Axiom sg_le_refl : forall (g : security_group), sg_le g g.
Axiom sg_le_trans : forall (g1 g2 g3 : security_group), sg_le g1 g2 -> sg_le g2 g3 -> sg_le g1 g3.
Axiom sg_le_antisym : forall (g1 g2 : security_group), sg_le g1 g2 -> sg_le g2 g1 -> g1 = g2.
Axiom sg_join_upper_bound_l : forall (g1 g2 : security_group), sg_le g1 (sg_join g1 g2).
Axiom sg_join_upper_bound_r : forall (g1 g2 : security_group), sg_le g2 (sg_join g1 g2).
Axiom sg_join_least_upper_bound : forall (g1 g2 g3 : security_group), sg_le g1 g3 -> sg_le g2 g3 -> sg_le (sg_join g1 g2) g3.

Record security_prop : Type := MkSP {
  r  : security_group;
  ir : security_group;
}.

Inductive ty : Type :=
  | Ty_Unit : ty
  | Ty_Sum  : sec_type -> sec_type -> ty
  | Ty_Prod : sec_type -> sec_type -> ty
  | Ty_Arrow: sec_type -> sec_type -> ty
with sec_type : Type :=
  | Mk_sec_type : ty -> security_prop -> sec_type.

Definition var : Type := string.

Inductive term : Type :=
  | T_Var     : var -> term
  | T_Unit    : security_prop -> term
  | T_Lam     : var -> sec_type -> term -> security_prop -> term
  | T_Pair    : term -> term -> security_prop -> term
  | T_Inj     : bool -> term -> security_prop -> term
  | T_App     : term -> term -> security_group -> term
  | T_Proj    : bool -> term -> security_group -> term
  | T_Case    : term -> var -> term -> var -> term -> security_group -> term
  | T_Protect : security_group -> term -> term
  | T_Rec     : var -> sec_type -> term -> term.

Inductive is_value : term -> Prop :=
  | V_Unit : forall k,
      is_value (T_Unit k)
  | V_Lam : forall x s e k,
      is_value (T_Lam x s e k)
  | V_Pair : forall v1 v2 k,
      is_value v1 -> is_value v2 -> is_value (T_Pair v1 v2 k)
  | V_Inj : forall i v k,
      is_value v -> is_value (T_Inj i v k).

Fixpoint subst (e : term) (x : var) (v : term) : term :=
  match e with
  | T_Var y =>
      if string_dec y x then v else T_Var y
  | T_Unit k => T_Unit k
  | T_Lam y s body k =>
      if string_dec y x then T_Lam y s body k
      else T_Lam y s (subst body x v) k
  | T_Pair e1 e2 k => T_Pair (subst e1 x v) (subst e2 x v) k
  | T_Inj i e k => T_Inj i (subst e x v) k
  | T_App e1 e2 r => T_App (subst e1 x v) (subst e2 x v) r
  | T_Proj i e r => T_Proj i (subst e x v) r
  | T_Case e x1 e1 x2 e2 r =>
      let e' := subst e x v in
      let e1' := if string_dec x1 x then e1 else subst e1 x v in
      let e2' := if string_dec x2 x then e2 else subst e2 x v in
      T_Case e' x1 e1' x2 e2' r
  | T_Protect ir' e => T_Protect ir' (subst e x v)
  | T_Rec f s body =>
      if string_dec f x then T_Rec f s body
      else T_Rec f s (subst body x v)
  end.

Definition sp_join (k : security_prop) (ir' : security_group) : security_prop :=
  MkSP (sg_join k.(r) ir') (sg_join k.(ir) ir').

Definition protect_val (v : term) (ir' : security_group) : option term :=
  match v with
  | T_Unit k => Some (T_Unit (sp_join k ir'))
  | T_Lam x s e k => Some (T_Lam x s e (sp_join k ir'))
  | T_Pair v1 v2 k => Some (T_Pair v1 v2 (sp_join k ir'))
  | T_Inj i v' k => Some (T_Inj i v' (sp_join k ir'))
  | _ => None
  end.

Inductive step : term -> term -> Prop :=
  | Step_App : forall x s e k v r' ir' v_body,
      is_value v ->
      let k_fun := MkSP r' ir' in
      k = k_fun -> (* Match the (r,ir) from the paper *)
      sg_le r' r' -> (* r \sqsubseteq r' *)
      v_body = T_Protect ir' (subst e x v) ->
      step (T_App (T_Lam x s e k) v r') v_body
  | Step_Proj : forall i v1 v2 k r' ir' v_i,
      is_value v1 ->
      is_value v2 ->
      let k_pair := MkSP r' ir' in
      k = k_pair ->
      sg_le r' r' -> (* r \sqsubseteq r' *)
      v_i = (if (i : bool) then v2 else v1) ->
      step (T_Proj i (T_Pair v1 v2 k) r') (T_Protect ir' v_i)
  | Step_Case : forall i v k x1 e1 x2 e2 r' ir' v_body,
      is_value v ->
      let k_sum := MkSP r' ir' in
      k = k_sum ->
      sg_le r' r' -> (* r \sqsubseteq r' *)
      v_body = (if (i : bool)
                then T_Protect ir' (subst e2 x2 v)
                else T_Protect ir' (subst e1 x1 v)) ->
      step (T_Case (T_Inj i v k) x1 e1 x2 e2 r') v_body
  | Step_Rec : forall f s e,
      step (T_Rec f s e) (subst e f (T_Rec f s e))
  | Step_Protect : forall ir' v v',
      is_value v ->
      protect_val v ir' = Some v' ->
      step (T_Protect ir' v) v'

  (* Congruence Rules (from Evaluation Contexts E) [cite: 121-123] *)
  | Cong_App1 : forall e1 e1' e2 r,
      step e1 e1' ->
      step (T_App e1 e2 r) (T_App e1' e2 r)
  | Cong_App2 : forall v1 e2 e2' r,
      is_value v1 ->
      step e2 e2' ->
      step (T_App v1 e2 r) (T_App v1 e2' r)
  | Cong_Proj : forall i e e' r,
      step e e' ->
      step (T_Proj i e r) (T_Proj i e' r)
  | Cong_Pair1 : forall e1 e1' e2 k,
      step e1 e1' ->
      step (T_Pair e1 e2 k) (T_Pair e1' e2 k)
  | Cong_Pair2 : forall v1 e2 e2' k,
      is_value v1 ->
      step e2 e2' ->
      step (T_Pair v1 e2 k) (T_Pair v1 e2' k)
  | Cong_Inj : forall i e e' k,
      step e e' ->
      step (T_Inj i e k) (T_Inj i e' k)
  | Cong_Case : forall e e' x1 e1 x2 e2 r,
      step e e' ->
      step (T_Case e x1 e1 x2 e2 r) (T_Case e' x1 e1 x2 e2 r)
  | Cong_Protect : forall ir' e e',
      step e e' ->
      step (T_Protect ir' e) (T_Protect ir' e').

Definition sp_le (k1 k2 : security_prop) : Prop :=
  sg_le k1.(r) k2.(r) /\ sg_le k1.(ir) k2.(ir).

Inductive sty_le : sec_type -> sec_type -> Prop :=
  | Sub_Unit : forall k1 k2,
      sp_le k1 k2 ->
      sty_le (Mk_sec_type Ty_Unit k1) (Mk_sec_type Ty_Unit k2)
  | Sub_Sum : forall s1 s1' s2 s2' k1 k2,
      sty_le s1 s1' ->
      sty_le s2 s2' ->
      sp_le k1 k2 ->
      sty_le (Mk_sec_type (Ty_Sum s1 s2) k1) (Mk_sec_type (Ty_Sum s1' s2') k2)
  | Sub_Prod : forall s1 s1' s2 s2' k1 k2,
      sty_le s1 s1' ->
      sty_le s2 s2' ->
      sp_le k1 k2 ->
      sty_le (Mk_sec_type (Ty_Prod s1 s2) k1) (Mk_sec_type (Ty_Prod s1' s2') k2)
  | Sub_Arrow : forall s1 s1' s2 s2' k1 k2,
      sty_le s1' s1 ->
      sty_le s2 s2' ->
      sp_le k1 k2 ->
      sty_le (Mk_sec_type (Ty_Arrow s1 s2) k1) (Mk_sec_type (Ty_Arrow s1' s2') k2)
  | Sub_Refl : forall s,
      sty_le s s
  | Sub_Trans : forall s1 s2 s3,
      sty_le s1 s2 -> sty_le s2 s3 -> sty_le s1 s3.

Definition context := list (var * sec_type).

Definition lookup (G : context) (x : var) : option sec_type :=
  find (fun p => string_dec (fst p) x) G.

Definition sty_protect (s : sec_type) (ir' : security_group) : sec_type :=
  (fst s, sp_join (snd s) ir').

Inductive has_type : context -> term -> sec_type -> Prop :=
  | T_Var_Rule : forall G x s,
      lookup G x = Some s ->
      has_type G (T_Var x) s
  | T_Unit_Rule : forall G k,
      has_type G (T_Unit k) (Ty_Unit, k)
  | T_Sub_Rule : forall G e s s',
      has_type G e s ->
      sty_le s s' ->
      has_type G e s'
  | T_Rec_Rule : forall G f s e,
      (fst s = Ty_Arrow (fst s) (fst s)) -> (* Check s is a function type *)
      has_type ((f, s) :: G) e s ->
      has_type G (T_Rec f s e) s
  | T_Lam_Rule : forall G x s1 e s2 k,
      has_type ((x, s1) :: G) e s2 ->
      has_type G (T_Lam x s1 e k) (Ty_Arrow (fst s1) (fst s2), k)
  | T_App_Rule : forall G e1 e2 r' s1 s2 r_fun ir_fun,
      let k_fun := MkSP r_fun ir_fun in
      has_type G e1 (Ty_Arrow (fst s1) (fst s2), k_fun) ->
      has_type G e2 s1 ->
      sg_le r_fun r' ->
      has_type G (T_App e1 e2 r') (sty_protect s2 ir_fun)
  | T_Pair_Rule : forall G e1 e2 s1 s2 k,
      has_type G e1 s1 ->
      has_type G e2 s2 ->
      has_type G (T_Pair e1 e2 k) (Ty_Prod (fst s1) (fst s2), k)
  | T_Proj_Rule : forall G i e r' s1 s2 r_pair ir_pair,
      let k_pair := MkSP r_pair ir_pair in
      has_type G e (Ty_Prod (fst s1) (fst s2), k_pair) ->
      sg_le r_pair r' ->
      let s_i := if i then s2 else s1 in
      has_type G (T_Proj i e r') (sty_protect s_i ir_pair)
  | T_Inj_Rule : forall G i e s1 s2 k,
      let s_i := if i then s2 else s1 in
      has_type G e s_i ->
      has_type G (T_Inj i e k) (Ty_Sum (fst s1) (fst s2), k)
  | T_Case_Rule : forall G e x1 e1 x2 e2 r' s s1 s2 r_sum ir_sum,
      let k_sum := MkSP r_sum ir_sum in
      has_type G e (Ty_Sum (fst s1) (fst s2), k_sum) ->
      has_type ((x1, s1) :: G) e1 s ->
      has_type ((x2, s2) :: G) e2 s ->
      sg_le r_sum r' -> (* r \sqsubseteq r' *)
      has_type G (T_Case e x1 e1 x2 e2 r') (sty_protect s ir_sum)
  | T_Protect_Rule : forall G ir' e s,
      has_type G e s ->
      has_type G (T_Protect ir' e) (sty_protect s ir').

Ltac admit := idtac "Proof omitted.". (* "sorry" *)

Lemma canonical_forms_lam : forall v s1 s2 k,
  is_value v ->
  has_type [] v (Ty_Arrow s1 s2, k) ->
  exists x, exists s, exists e, exists k',
    v = T_Lam x s e k'.
Proof. admit. Defined.

Lemma canonical_forms_prod : forall v s1 s2 k,
  is_value v ->
  has_type [] v (Ty_Prod s1 s2, k) ->
  exists v1, exists v2, exists k',
    v = T_Pair v1 v2 k'.
Proof. admit. Defined.

Lemma canonical_forms_sum : forall v s1 s2 k,
  is_value v ->
  has_type [] v (Ty_Sum s1 s2, k) ->
  exists i, exists v', exists k',
    v = T_Inj i v' k'.
Proof. admit. Defined.

Theorem substitution_lemma : forall G e x s' v s,
  has_type ((x, s') :: G) e s ->
  has_type [] v s' ->
  has_type G (subst e x v) s.
Proof.
  admit.
Defined.

Theorem preservation : forall e e' s,
  has_type [] e s ->
  step e e' ->
  has_type [] e' s.
Proof.
  admit.
Defined.

Theorem progress : forall e s,
  has_type [] e s ->
  is_value e \/ (exists e', step e e').
Proof.
  admit.
Defined.