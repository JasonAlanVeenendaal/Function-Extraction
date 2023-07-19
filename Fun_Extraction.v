From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Basics.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Imp.
From PLF Require Import Maps.
From Coq Require Import Lists.List.
From PLF Require Import Hoare.
From Coq Require Import Lia.
From Coq Require Import FinFun. 
Import ListNotations.

Open Scope string.
Locate length.
Locate t_update.

Search (string_dec _ _ = true).

Inductive token : Type :=
  | FunctionToken (s : string)
  | VariableToken (s : string).

Fixpoint t_update_list {A : Type} (m : total_map A) (x : list string) (v : list A) :=
  match x, v with
  | [], [] => m
  | [], _ => m
  | _, [] => m
  | h1::t1, h2::t2 => t_update (t_update_list m t1 t2) h1 h2
  end.

(* The first entry in the tuple is the function environment. The second entry is the variable environment. *)
Definition token_update  {A : Type} (m : prod (total_map A) (total_map A)) (x : token) (v : A) :=
  match x with
  | FunctionToken s => (t_update (fst m) s v, snd m)
  | VariableToken s => (fst m, t_update (snd m) s v)
  end.

Fixpoint token_update_list {A : Type} (m : prod (total_map A) (total_map A)) (x : list token) (v : list A) :=
  match x, v with
  | h1::t1, h2::t2 => token_update (token_update_list m t1 t2) h1 h2
  | _, _ => m
  end.

Definition token_to_string (x : token) :=
  match x with
  | FunctionToken s => s
  | VariableToken s => s
  end.

Definition empty_st := (_ !-> 0).
Check t_update_list.

(*
redundant

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AVar (s : string).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
*)

Inductive function : Type :=
  | Num (n : nat)
  | Plus (f g : function)
  | Minus (f g : function)
  | Mult (f g : function)
  | Bool (b : bool)
  | Eq (f g : function)
  | Neq (f g : function)
  | LessEq (f g : function)
  | Greater (f g : function)
  | Not (f : function)
  | And (f g : function)
  | Vars (ls : list token)
  | Let (lhs : token) (rhs : function) (inthis : function)
  | If (premise: function) (f : function) (g : function)
  | Lambda (args : list token) (f : function)
  | Application (f : function) (g : function)
  | Rec (name : token) (bind : list token) (body : function).

Locate "|->".
Definition Whilefun h g args := Rec (FunctionToken "Whilefun") args
(If (Application h (Vars args)) (Application (Vars [(FunctionToken "Whilefun")]) (Application g (Vars args))) (Vars args)).


Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Definition example : com :=
  CSeq (CAsgn ("y") (ANum 1)) (CWhile (BGt(AId "x")(ANum 0))(CSeq (CAsgn ("y")(AMult(AId "x")(AId "y")))((CAsgn ("x")(AMinus(AId "x")(ANum 1)))))).

Notation "\ x . y " := (Lambda x y) (at level 50).

(* don't need this

Inductive Option (A : Type) : Type :=
  | Just : A -> Option A
  | Nothing : Option A.

Definition assertion := total_map (Option function).

Definition empty_assertion : assertion :=
  fun _ => Nothing function.

*)


Fixpoint aimp_to_functional (a : aexp) : function :=
  match a with
  | ANum n => Num n
  | APlus a1 a2 => Plus (aimp_to_functional a1) (aimp_to_functional a2)
  | AMinus a1 a2 => Minus (aimp_to_functional a1) (aimp_to_functional a2)
  | AMult a1 a2 => Mult (aimp_to_functional a1) (aimp_to_functional a2)
  | AId s => Vars [(VariableToken s)]
  end.

Fixpoint bimp_to_functional (b : bexp) : function := 
  match b with 
  | BTrue => Bool true
  | BFalse => Bool false
  | BEq a1 a2 => Eq (aimp_to_functional a1) (aimp_to_functional a2)
  | BNeq a1 a2 => Neq (aimp_to_functional a1) (aimp_to_functional a2)
  | BLe a1 a2 => LessEq (aimp_to_functional a1) (aimp_to_functional a2)
  | BGt a1 a2 => Greater (aimp_to_functional a1) (aimp_to_functional a2)
  | BNot b => Not (bimp_to_functional b)
  | BAnd b1 b2 => And (bimp_to_functional b1) (bimp_to_functional b2)
  end.

Fixpoint get_vars (a : aexp) : list string :=
  match a with
  | ANum n => []
  | APlus a1 a2 => (get_vars a1) ++ (get_vars a2)
  | AMinus a1 a2 => (get_vars a1) ++ (get_vars a2)
  | AMult a1 a2 => (get_vars a1) ++ (get_vars a2)
  | AId s => [(s)]
  end.

Fixpoint get_bvars (b : bexp) : list string :=
  match b with
  | BTrue => []
  | BFalse => []
  | BEq a1 a2 => (get_vars a1) ++ (get_vars a2)
  | BNeq a1 a2 => (get_vars a1) ++ (get_vars a2)
  | BLe a1 a2 => (get_vars a1) ++ (get_vars a2)
  | BGt a1 a2 => (get_vars a1) ++ (get_vars a2)
  | BNot b => get_bvars b
  | BAnd b1 b2 => (get_bvars b1) ++ (get_bvars b2)
  end.

Fixpoint get_variables (c : com) : list string :=
  match c with
  | CAsgn x a => [(x)] ++ (get_vars a)
  | CSkip => []
  | CSeq c1 c2 => (get_variables c1) ++ (get_variables c2)
  | CIf b c1 c2 => (get_bvars b) ++ (get_variables c1) ++ (get_variables c2)
  | CWhile b c => (get_bvars b) ++ (get_variables c)
  end.

Fixpoint get_function_variables (f : function) : list token :=
  match f with
  | Num n => []
  | Plus f g => (get_function_variables f) ++ (get_function_variables g)
  | Minus f g => (get_function_variables f) ++ (get_function_variables g)
  | Mult f g => (get_function_variables f) ++ (get_function_variables g)
  | Bool b => []
  | Eq f g => (get_function_variables f) ++ (get_function_variables g)
  | Neq f g => (get_function_variables f) ++ (get_function_variables g)
  | LessEq f g => (get_function_variables f) ++ (get_function_variables g)
  | Greater f g => (get_function_variables f) ++ (get_function_variables g)
  | Not f => get_function_variables f
  | And f g => (get_function_variables f) ++ (get_function_variables g)
  | Vars ls => ls
  | Let lhs rhs inthis => lhs :: ((get_function_variables rhs) ++ (get_function_variables inthis))
  | If premise f g => (get_function_variables premise) ++ (get_function_variables f) ++ (get_function_variables g)
  | Lambda args f => args ++ (get_function_variables f)
  | Application f g => (get_function_variables f) ++ (get_function_variables g)
  | Rec name bind body => name :: (bind ++ get_function_variables body)
  end.


Fixpoint element_of (s : string) (l : list string) : bool :=
  match l with
  | nil => false
  | x::xs => if (x =? s) then true else (element_of s xs)
  end.

Fixpoint remove_dup (l : list string) : list string :=
  match l with
  | nil => []
  | x::xs => if (element_of x (remove_dup xs)) then (remove_dup xs) else (x::(remove_dup xs))
  end.

Fixpoint extract_fun (c : com) (args0 : list string) : function :=
  let args := map VariableToken args0 in 
  match c with
  | CAsgn x a => Lambda (args) (Let (VariableToken x) (aimp_to_functional a) (Vars args))
  | CSkip => Lambda (args) (Vars args)
  | CSeq c1 c2 => Lambda (args) (Application (extract_fun c2 args0) (Application (extract_fun c1 args0) (Vars args)))
  | CIf b c1 c2 => Lambda (args) (If (bimp_to_functional b) (Application (extract_fun c1 args0) (Vars args)) (Application (extract_fun c2 args0) (Vars args)))
  | CWhile b c => Whilefun (Lambda (args) (bimp_to_functional b)) (extract_fun c args0) (args)
  end.

Notation " < x > < y >" := (Application x y) (at level 49).

Compute get_variables example.
Compute remove_dup (get_variables example).
Compute extract_fun example ((remove_dup ((get_variables example)))).



Definition function_example := extract_fun example ((remove_dup ((get_variables example)))).

Definition variable_extraction (c : com) := (remove_dup ((get_variables c))).

Definition decompile (c : com) : function := extract_fun c (variable_extraction c).

Inductive value : Type := 
  | Number (n : nat)
  | Boolean (b : bool)
  | Closure (name : (option token)) (args : list token) (body : function) (env : prod (total_map value) (total_map value))
  | FreeVariable (x : token).

Fixpoint map_over_tokens (m : prod (total_map value) (total_map value)) (x : list token) :=
  match x with
  | [] => []
  | h :: t => match h with
              | VariableToken s => (snd m) s :: (map_over_tokens m t)
              | FunctionToken s => (fst m) s :: (map_over_tokens m t)
              end
  end.

Fixpoint equals (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S l, 0 => false
  | 0, S k => false
  | S l, S k => equals l k
  end.

Fixpoint less (n m: nat) : bool :=
  match n, m with
  | 0, 0 => false
  | S l, 0 => false
  | 0, S k => true
  | S l, S k => less l k
  end.

Fixpoint eval (rho : prod (total_map value) (total_map value)) (e : function) (fuel : nat) : (option (list value)):=
  match fuel with
  | S k => 
  match e with 
  | Num n => Some [Number n]
  | Plus f g => match (eval rho f k), (eval rho g k) with
                | Some [Number m], Some [Number l] => Some [Number (m+l)]
                | _, _ => None
                end
  | Minus f g => match (eval rho f k) with
                | Some [Number m] => match (eval rho g k) with
                              | Some [Number l] => Some [Number (m-l)]
                              | _ => None
                              end
                | _ => None
                end
  | Mult f g => match (eval rho f k) with
                | Some [Number m] => match (eval rho g k) with
                              | Some [Number l] => Some [Number (m*l)]
                              | _ => None
                              end
                | _ => None
                end
  | Bool v => Some [Boolean v]
  | Vars l => Some (map_over_tokens rho l)
  | Let lhs rhs inthis => match eval rho rhs k with
                          | Some v =>  eval (token_update_list rho [lhs] (v)) inthis k
                          | _ => None
                          end
  | Lambda args f => Some [Closure None args f rho]
  | Application f g => match eval rho f k, eval rho g k with
                       | Some [Closure name args body psi], Some lv =>
                              match name with
                              | Some tkn => eval (token_update_list psi (tkn::args) ((Closure (Some tkn) args body psi)::lv)) body k
                              | None => eval (token_update_list psi args lv) body k
                              end
                       | _ , _ => None
                       end
  | If premise f g => match eval rho premise k with
                      | Some [Boolean true] => eval rho f k
                      | Some [Boolean false] => eval rho g k
                      | _ => None
                      end
  | Rec name bind body => Some [Closure (Some name) bind body rho]
  | Not f => match eval rho f k with
             | Some [Boolean false] => Some [Boolean true]
             | Some [Boolean true] => Some [Boolean false]
             | _ => None
             end
  | And f g => match eval rho f k, eval rho g k with
               | Some [Boolean true], Some [Boolean true] => Some [Boolean true]
               | Some [Boolean true], Some [Boolean false] => Some [Boolean false]
               | Some [Boolean false], Some [Boolean false] => Some [Boolean false]
               | Some [Boolean false], Some [Boolean true] => Some [Boolean false]
               | _, _ => None
               end
  | Eq f g => match eval rho f k, eval rho g k with
              | Some [Number n], Some [Number m] => Some [Boolean (n =? m)%nat]
              | _, _ => None
              end
  | LessEq f g => match eval rho f k, eval rho g k with
                | Some [Number n], Some [Number m] => Some [Boolean (n <=? m)%nat]
                | _, _ => None
                end
  | Greater f g => match eval rho f k, eval rho g k with
                | Some [Number n], Some [Number m] => Some [Boolean (m <? n)%nat]
                | _, _ => None
                end
  | Neq f g => match eval rho f k, eval rho g k with
              | Some [Number n], Some [Number m] => Some [Boolean (negb (n =? m)%nat)]
              | _, _ => None
              end
  end
  | 0 => None
  end.


Check compose Number empty_st.
Check total_map value.

Lemma split_plus1 : forall a1 a2 st, (aeval st a1) + (aeval st a2) = (aeval st <{a1 + a2}>).
Proof.
  intros a1 a2 st. simpl. reflexivity.
Qed.

(*
THIS WAS PROVEN FROM THE OLD EVAL

Lemma vars_one : forall x rho, (length x > 0) -> ((eval rho (Vars x) (length x)) = Just (map rho x)).
Proof.
intros x rho.
induction x.
- intros H. simpl in H. simpl. lia.
- intros H. apply list_plus_one in H. destruct H. rewrite H.
  destruct x.
  -- simpl. reflexivity.
  -- simpl eval. assert (need : length (s::x) > 0).
     --- simpl. destruct x.
         ---- simpl. lia.
         ---- simpl. lia.
     --- specialize (IHx need). assert (need2 : length (s::x) = x0).
         ---- unfold length in H. injection H. unfold length. intros HH. apply HH.
         ---- rewrite need2 in IHx. rewrite IHx. unfold map. reflexivity.
Qed.
*)

Lemma vars_reduce : forall x rho v n, ((eval rho (Vars x) n) = Some v) -> (map_over_tokens rho x = v).
Proof.
  intros x rho v n H.
  induction n. simpl in H; try discriminate.
  simpl in H; try discriminate. injection H as H. apply H.
Qed.


Definition empty_environment : (prod (total_map value) (total_map value)) :=
  (fun x => FreeVariable (FunctionToken x), fun x => FreeVariable (VariableToken x)).

Definition set_variable (x : string) (y : value) : (prod (total_map value) (total_map value)) :=
  (fst empty_environment, t_update (snd empty_environment) x y).

Definition set_variables (x : list string) (y : list value) : (prod (total_map value) (total_map value)) :=
  (fst empty_environment, t_update_list (snd empty_environment) x y).

Compute (snd empty_environment) ("x").
Compute function_example.
Compute eval empty_environment (Application function_example (Vars [VariableToken "y"; VariableToken "x"])) 1000.

Definition test1 :=
  Application (Lambda [VariableToken "x"] (Vars [VariableToken "x"])) (Num 1).

Compute eval empty_environment test1 3.
Compute eval empty_environment (Num 5) 3.
Compute (snd (set_variable ("x") (Number 5))) "x".
Compute eval (set_variable ("x") (Number 0)) (Application function_example (Vars [VariableToken "y"; VariableToken "x"])) 18.
Compute eval (set_variable ("x") (Number 5)) (Application function_example (Vars [VariableToken "y"; VariableToken "x"])) 18.

Fixpoint factorial  (n : nat) :=
  match n with
  | 0 => 1
  | S m => n * (factorial m)
end.

Lemma eval_eq : forall rho e fuel, (eval (rho : prod (total_map value) (total_map value)) (e : function) (fuel : nat) : (option (list value))) =
  (match fuel with
  | S k => 
  match e with 
  | Num n => Some [Number n]
  | Plus f g => match (eval rho f k), (eval rho g k) with
                | Some [Number m], Some [Number l] => Some [Number (m+l)]
                | _, _ => None
                end
  | Minus f g => match (eval rho f k) with
                | Some [Number m] => match (eval rho g k) with
                              | Some [Number l] => Some [Number (m-l)]
                              | _ => None
                              end
                | _ => None
                end
  | Mult f g => match (eval rho f k) with
                | Some [Number m] => match (eval rho g k) with
                              | Some [Number l] => Some [Number (m*l)]
                              | _ => None
                              end
                | _ => None
                end
  | Bool v => Some [Boolean v]
  | Vars l => Some (map_over_tokens rho l)
  | Let lhs rhs inthis => match eval rho rhs k with
                          | Some v =>  eval (token_update_list rho [lhs] (v)) inthis k
                          | _ => None
                          end
  | Lambda args f => Some [Closure None args f rho]
  | Application f g => match eval rho f k, eval rho g k with
                       | Some [Closure name args body psi], Some lv =>
                              match name with
                              | Some tkn => eval (token_update_list psi (tkn::args) ((Closure (Some tkn) args body psi)::lv)) body k
                              | None => eval (token_update_list psi args lv) body k
                              end
                       | _ , _ => None
                       end
  | If premise f g => match eval rho premise k with
                      | Some [Boolean true] => eval rho f k
                      | Some [Boolean false] => eval rho g k
                      | _ => None
                      end
  | Rec name bind body => Some [Closure (Some name) bind body rho]
  | Not f => match eval rho f k with
             | Some [Boolean false] => Some [Boolean true]
             | Some [Boolean true] => Some [Boolean false]
             | _ => None
             end
  | And f g => match eval rho f k, eval rho g k with
               | Some [Boolean true], Some [Boolean true] => Some [Boolean true]
               | Some [Boolean true], Some [Boolean false] => Some [Boolean false]
               | Some [Boolean false], Some [Boolean false] => Some [Boolean false]
               | Some [Boolean false], Some [Boolean true] => Some [Boolean false]
               | _, _ => None
               end
  | Eq f g => match eval rho f k, eval rho g k with
              | Some [Number n], Some [Number m] => Some [Boolean (n =? m)%nat]
              | _, _ => None
              end
  | LessEq f g => match eval rho f k, eval rho g k with
                | Some [Number n], Some [Number m] => Some [Boolean (n <=? m)%nat]
                | _, _ => None
                end
  | Greater f g => match eval rho f k, eval rho g k with
                | Some [Number n], Some [Number m] => Some [Boolean (m <? n)%nat]
                | _, _ => None
                end
  | Neq f g => match eval rho f k, eval rho g k with
              | Some [Number n], Some [Number m] => Some [Boolean (negb (n =? m)%nat)]
              | _, _ => None
              end
  end
  | 0 => None
  end).
Proof.
  Admitted.

Lemma decompose_prod : forall env : prod (total_map value) (total_map value), env = (fst env, snd env).
Proof.
  intros.
  destruct env.
  simpl. auto.
Qed.


Definition new_example : com :=  <{ "x" := 3;  if ("x" <> 5) then "x" := 5 else "x" := 4 end }>.
Definition new_function_example := decompile new_example.
Compute new_function_example.


Compute new_example.

Compute eval (set_variable ("x") (Number 5)) (Application new_function_example (Vars [VariableToken "x"])) 25.

Compute function_example.

Definition assgn5 :=  eval empty_environment (Application (decompile <{ "x" := 5 }>) (Vars [VariableToken "x"])) 3.

Fixpoint make_conjunction (X : list string) (v : list nat) : Assertion :=
  fun st => match X, v with 
            | [], [] => True
            | [], _ => False
            | _, [] => False
            | h1::t1, h2::t2 => ((st h1) = h2) /\ ((make_conjunction t1 t2) st)
            end.

Theorem equals_string : forall x, x =? x = true.
Proof.
  Search "=?". intros x. apply eqb_eq. reflexivity.
  Qed.

Lemma less_than : forall X v, (length X < length v) ->
                  (make_conjunction X v  ->> fun st => False).
Proof.
  intros X. induction X as [| x xs IHX'].
  - intros v H. simpl.
    destruct v.
    -- simpl in H. lia.
    -- unfold "->>". intros H1 H2. apply H2.
  - intros v H. unfold make_conjunction. unfold make_conjunction in IHX'.
    destruct v as [| h t].
    -- unfold "->>". intros H1 H2. apply H2.
    -- specialize IHX' with (v:=t).
       simpl in H. pose lt_S_n as H2.
       specialize H2 with (length xs) (length t).
       apply H2 in H. apply IHX' in H. unfold "->>".
       intros st H3. destruct H3. unfold "->>" in H.
       specialize H with (st:=st). apply H in H1. apply H1.
Qed.

Lemma greater_than : forall X v, (length X > length v) ->
                     (make_conjunction X v ->> fun st => False).
Proof.
  intros X. induction X as [| x xs IHX'].
  - intros v H. simpl.
    destruct v.
    -- simpl in H. lia.
    -- unfold "->>". intros H1 H2. apply H2.
  - intros v H.
    destruct v as [| h t].
    -- unfold "->>". unfold make_conjunction. intros H1 H2.
       apply H2.
    -- specialize IHX' with (v:=t).
       simpl in H. pose gt_S_n as H2.
       specialize H2 with (length t) (length xs).
       apply H2 in H. apply IHX' in H. unfold "->>".
       intros st H3. unfold make_conjunction in H3.
       destruct H3. unfold "->>" in H. unfold make_conjunction in H.
       specialize H with (st:=st). apply H in H1. apply H1.
Qed.


Lemma not_equals : forall (A : Type) (f : list A), f <> f -> False.
Proof.
  intros A f. intros H. destruct H. reflexivity.
  Qed.

Fixpoint duplicates_in (X : list string) : bool :=
  match X with 
  | [] => false
  | x :: xs => orb (element_of x xs) (duplicates_in xs)
  end.

(*
Lemma duplicated : forall X v, (length X = length v) ->
                               (NoDup X) ->
                               (map
                                  (t_update_list empty_environment X
                                     (map Number v)) X) = (map Number v).
Proof.
Admitted.
*)

Lemma unused_variable : forall x xs v (m : total_map value), ~In x xs -> map (t_update m x v) xs = map m xs.
Proof.
  intros x xs. induction xs.
  - simpl. auto.
  - intros v m H. simpl. f_equal.
    -- apply t_update_neq. simpl in H. auto.
    -- apply IHxs. simpl in H. auto.
Qed.

Lemma unused_variable_token_version : forall x xs v s (m : (total_map value * total_map value)), ~In x xs ->
FunctionToken s = x ->
map_over_tokens
  (fun x' : string => if s =? x' then v else fst m x', snd m) xs = map_over_tokens m xs.
Proof.
  intros x xs. induction xs as [| h t].
  - simpl. auto.
  - intros. simpl.
    destruct h.
    -- Search In. eapply not_in_cons in H. destruct H. subst.
       assert (s <> s0). { congruence. } Search "=?". eapply eqb_neq in H0. erewrite H0.
       apply f_equal. eapply IHt. 2:auto. auto.
    -- apply f_equal. apply IHt. 2:auto. Search In. eapply not_in_cons in H. destruct H. auto.
Qed.

Lemma unused_variable_token_version_snd : forall x xs v s (m : (total_map value * total_map value)), ~In x xs ->
VariableToken s = x ->
map_over_tokens
  (fst m,
  fun x' : string =>
  if s =? x' then v else snd m x') xs = map_over_tokens m xs.
Proof.
  intros x xs. induction xs as [| h t].
  - simpl. auto.
  - intros. simpl.
    destruct h.
    -- apply f_equal. eapply not_in_cons in H. destruct H. eapply IHt. 2:auto. auto.
    -- eapply not_in_cons in H. destruct H. subst. assert (s <> s0). { congruence. }
       eapply eqb_neq in H0. erewrite H0. apply f_equal. eapply IHt. 2:auto. auto.
Qed.


Lemma not_in : forall (x : string) xs, (NoDup (x::xs)) -> (~ In x xs).
Proof.
  intros x xs H. Search NoDup. apply NoDup_cons_iff. apply H.
Qed.

Lemma step_gen : forall X v (env : total_map value), (length X = length v) ->
                         (NoDup X) ->
                         (map
                         (t_update_list env X
                         v) X) = v.
Proof.
  intros X. induction X as [| x xs IHX'].
  - simpl. intros v eq. unfold length in eq. destruct v.
    -- reflexivity.
    -- discriminate.
  - intros v env eq H.
    destruct v as [| h t] eqn : E.
    -- discriminate.
    -- assert (need : length xs = length t).
       { simpl length in eq. injection eq as eq. apply eq. }
       specialize IHX' with (env:=env) (v := t). simpl. simpl in IHX'.
       specialize (IHX' need). simpl in IHX'. rewrite t_update_eq.
       apply f_equal. rewrite unused_variable.
       --- apply IHX'. Search NoDup. apply NoDup_cons_iff in H. destruct H. apply H0.
       --- apply not_in. apply H.
Qed.

Lemma step : forall X v (env : (total_map value * total_map value)), (length X = length v) ->
                         (NoDup X) ->
                         (map
                         (t_update_list (snd env) X
                         (map Number v)) X) = (map Number v).
Proof.
  intros; eapply step_gen; auto. Search map. rewrite map_length. auto.
Qed.

Lemma destruct_length : forall n m, (n < m) \/ (n > m) \/ (n = m).
Proof.
  lia.
Qed.

Lemma conjunction_implication : forall x hv' n ts, (make_conjunction [x] (hv' :: n :: ts)) ->> (make_conjunction [x] [hv']).
Proof.
  intros x hv' n ts. unfold make_conjunction. unfold "->>". intros st. intros H. destruct H. split.
  - apply H.
  - auto.
Qed.

Lemma needed_for_reduce_again : forall (X : list string) (Y : list value) m, (length X = length Y) ->
                                                                             (NoDup X) ->
                                              map (t_update_list m X Y) X = Y.
Proof.
  intros X Y m. revert Y m. induction X as [| x xs].
  - intros Y m H1 H2. simpl. Search length. symmetry in H1. apply length_zero_iff_nil in H1.
    auto.
  - intros Y m H1 H2.
    destruct Y as [| y ys].
    -- simpl in H1. lia.
    -- simpl. assert (H3 : (x !-> y; t_update_list m xs ys) x = y).
       { unfold "!->". Search "=?". rewrite equals_string. reflexivity. }
       rewrite H3. apply f_equal. rewrite unused_variable.
       --- specialize IHxs with (Y:=ys) (m:=m). apply IHxs.
           ---- simpl in H1. injection H1 as H1. apply H1.
           ---- Search NoDup. apply NoDup_cons_iff in H2. destruct H2. apply H0.
       --- apply not_in. apply H2.
Qed.

Lemma needed_for_reduce_again_token_version : forall (X : list token) (Y : list value) m, (length X = length Y) ->
NoDup X ->
map_over_tokens (token_update_list m X Y) X = Y.
Proof.
  induction X as [| x xs].
  - intros. simpl.
    destruct Y as [| y ys].
    -- auto.
    -- simpl in H. lia.
  - intros.
    destruct Y as [| y ys].
    -- simpl in H. lia.
    -- simpl.
       destruct x.
       --- unfold token_update. simpl. unfold "!->". erewrite eqb_refl. apply f_equal.
           erewrite unused_variable_token_version.
           ---- eapply IHxs.
                + simpl in H. lia.
                + Search NoDup. eapply NoDup_cons_iff in H0. destruct H0. auto.
           ---- Search NoDup. eapply NoDup_cons_iff in H0. destruct H0. apply H0.
           ---- auto.
       --- unfold token_update. simpl. unfold "!->". erewrite eqb_refl. apply f_equal.
           erewrite unused_variable_token_version_snd.
           ---- eapply IHxs.
                + simpl in H. auto.
                + eapply NoDup_cons_iff in H0. destruct H0. auto.
           ---- eapply NoDup_cons_iff in H0. destruct H0. apply H0.
           ---- auto.
Qed.

Lemma reduce_again : forall X Y, (length X = length Y) ->
                                 (NoDup X) ->
                                  map (t_update_list (t_update_list (snd empty_environment) X Y) X Y) X = Y.
Proof.
  intros X Y H1 H2. apply needed_for_reduce_again.
  - apply H1.
  - apply H2.
Qed.

Lemma unfold_map_Number : forall v v', map Number v = map Number v' -> v = v'.
Proof.
  intros v. induction v as [| v vs].
  - destruct v' as [| v' vs'].
    -- simpl. auto.
    -- intros H. simpl in H. inversion H.
  - destruct v' as [| v' vs'].
    -- simpl. intros H. inversion H.
    -- simpl. specialize IHvs with (v':=vs'). intros H. inversion H.
       specialize (IHvs H2). apply f_equal. apply IHvs.
Qed.


Lemma aeval_to_eval : forall st0 st a v, (exists n, eval (st0, compose Number st) (aimp_to_functional a) n = Some [v]) -> (Number (aeval st a) = v).
Proof.
  intros st0 st a. revert st. induction a.
  - intros st v H1. simpl in H1. simpl. destruct H1. destruct x; try discriminate. simpl in H. injection H as H. apply H.
  - intros st v H1. simpl in H1. simpl. destruct H1. destruct x0; try discriminate. simpl in H. injection H as H. auto.
  - intros st v H1. simpl in H1. simpl. destruct H1. destruct x; try discriminate. simpl in H.
    destruct (eval (st0, compose Number st) (aimp_to_functional a1) x) eqn : H2 in H; try discriminate.
    destruct l eqn : H3 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct (eval (st0, compose Number st) (aimp_to_functional a2) x) eqn : H4 in H; try discriminate.
    destruct l0 eqn : H5 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct l1; try discriminate. rewrite H3 in H2. rewrite H5 in H4.
    specialize IHa1 with (st:=st) (v:=Number n).
    specialize IHa2 with (st:=st) (v:=Number n0). injection H as H. rewrite <- H.
    apply f_equal. assert (H6 : (exists n0 : nat,
          eval (st0, compose Number st) (aimp_to_functional a1) n0 = Some [Number n])).
    { exists x. apply H2. }
    assert (H7 : (exists n : nat,
          eval (st0, compose Number st) (aimp_to_functional a2) n = Some [Number n0])).
    { exists x. apply H4. }
    specialize (IHa1 H6). specialize (IHa2 H7). injection IHa1 as IHa1. injection IHa2 as IHa2.
    auto.
  - intros st v H1. simpl in H1. simpl. destruct H1. destruct x; try discriminate. simpl in H.
    destruct (eval (st0, compose Number st) (aimp_to_functional a1) x) eqn : H2 in H; try discriminate.
    destruct l eqn : H3 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct (eval (st0, compose Number st) (aimp_to_functional a2) x) eqn : H4 in H; try discriminate.
    destruct l0 eqn : H5 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct l1; try discriminate. rewrite H3 in H2. rewrite H5 in H4.
    specialize IHa1 with (st:=st) (v:=Number n).
    specialize IHa2 with (st:=st) (v:=Number n0). injection H as H. rewrite <- H.
    apply f_equal. assert (H6 : (exists n0 : nat,
          eval (st0, compose Number st) (aimp_to_functional a1) n0 = Some [Number n])).
    { exists x. apply H2. }
    assert (H7 : (exists n : nat,
          eval (st0, compose Number st) (aimp_to_functional a2) n = Some [Number n0])).
    { exists x. apply H4. }
    specialize (IHa1 H6). specialize (IHa2 H7). injection IHa1 as IHa1. injection IHa2 as IHa2.
    auto.
  - intros st v H1. simpl in H1. simpl. destruct H1. destruct x; try discriminate. simpl in H.
    destruct (eval (st0, compose Number st) (aimp_to_functional a1) x) eqn : H2 in H; try discriminate.
    destruct l eqn : H3 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct (eval (st0, compose Number st) (aimp_to_functional a2) x) eqn : H4 in H; try discriminate.
    destruct l0 eqn : H5 in H; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct l1; try discriminate. rewrite H3 in H2. rewrite H5 in H4.
    specialize IHa1 with (st:=st) (v:=Number n).
    specialize IHa2 with (st:=st) (v:=Number n0). injection H as H. rewrite <- H.
    apply f_equal. assert (H6 : (exists n0 : nat,
          eval (st0, compose Number st) (aimp_to_functional a1) n0 = Some [Number n])).
    { exists x. apply H2. }
    assert (H7 : (exists n : nat,
          eval (st0, compose Number st) (aimp_to_functional a2) n = Some [Number n0])).
    { exists x. apply H4. }
    specialize (IHa1 H6). specialize (IHa2 H7). injection IHa1 as IHa1. injection IHa2 as IHa2.
    auto.
Qed.

Lemma needed_for_reduction : forall (x x0 : string) (y : value) (m : string -> value) X Y, ((x =? x0) = false) -> 
t_update_list (fun x' : string => if x =? x' then y else m x') X Y x0 = 
t_update_list (fun x' : string => m x') X Y x0.
Proof.
  intros x x0 y m X. revert x y x0 m. induction X as [| h t].
  - intros x x0 y m Y H1. simpl.
    destruct Y as [| h' t'].
    -- rewrite H1. auto.
    -- rewrite H1. auto.
  - intros x y x0 m Y H1.
    destruct Y as [| h' t'].
    -- simpl. rewrite H1. auto.
    -- specialize IHt with (x:=x) (y:=y) (m:=m) (x0:=x0) (Y:=t'). 
       specialize (IHt H1). unfold t_update_list. unfold t_update_list in IHt.
       unfold "!->".
       destruct (h =? x0).
       --- auto.
       --- unfold "!->" in IHt. rewrite IHt. auto.
Qed.

Lemma reduction : forall x y xs ys x0 (env : total_map value), (x !-> y; t_update_list (x !-> y; t_update_list env xs ys) xs ys) x0 =
(x !-> y; t_update_list env xs ys) x0.
Proof.
  intros x y xs. revert x y. induction xs as [| hxs txs].
  - simpl. intros x y ys x0.
    destruct ys.
    -- unfold "!->". destruct (x =? x0).
       --- auto.
       --- auto.
    -- unfold "!->". destruct (x =? x0).
       --- auto.
       --- auto.
  - intros x y ys x0 env. unfold "!->". unfold "!->" in IHtxs.
    destruct ys as [| hys tys] eqn : H.
    --
       simpl. destruct (x =? x0).
       --- reflexivity.
       --- reflexivity.
    -- specialize IHtxs with (x:=hxs) (y:=hys) (ys:=tys) (x0 := x0) (env:=env).
       simpl. destruct (x =? x0) eqn : H1.
       --- reflexivity.
       --- unfold "!->".
           destruct (hxs =? x0).
           ---- reflexivity.
           ---- rewrite <- IHtxs. 
                apply needed_for_reduction with (m:=fun x' : string => if hxs =? x'
   then hys
   else t_update_list env txs tys x'). apply H1.
Qed.

Lemma reduction_rewrite : forall x y xs ys (env : total_map value), (x !-> y; t_update_list (x !-> y; t_update_list env xs ys) xs ys) =
(x !-> y; t_update_list env xs ys).
Proof.
  intros x y xs ys env. apply functional_extensionality. intros x0. apply reduction.
Qed.

Lemma two_updates : forall X Y (env : total_map value), (t_update_list (t_update_list env X Y) X Y) = (t_update_list env X Y).
Proof.
  intros X. induction X as [| x xs].
  - intros Y. simpl.
    destruct Y.
    -- reflexivity.
    -- reflexivity.
  - intros Y.
    destruct Y as [| y ys].
    -- simpl. reflexivity.
    -- simpl. apply reduction_rewrite.
Qed.

Lemma needed_for_aimp : forall X v (x : string) l (env : (total_map value)) 
(Hsetvariables : map (env) X = (map Number v)),
(length X = length v) ->
(incl [x] X) ->
[(env) x] = l ->
(exists w, [Number w] = l).
Proof.
  intros X. induction X as [| h t].
  - intros v x l env Hsetvariables H1 H2. pose length_zero_iff_nil. unfold incl in H2.
    specialize H2 with (a:=x). assert (In x [x]).
                { unfold In. left. reflexivity. } specialize (H2 H). unfold In in H2. destruct H2.
  - intros v x l env Hsetvariables H1 H2 H3. pose in_inv. specialize o with (A:=string) (a:=h) (b:=x) (l:=t).
    unfold incl in H2. specialize H2 with (a:=x).
    assert (In x [x]).
    { unfold In. left. reflexivity. } specialize (H2 H). specialize (o H2).
    destruct v as [|v vs]; try discriminate.
    simpl in H3. unfold "!->" in H3.
    destruct o.
    -- rewrite <- H0 in H3. simpl in Hsetvariables. injection Hsetvariables as Hsetvariables.
       rewrite Hsetvariables in H3. exists v. auto.
    -- destruct (h =? x) eqn : E.
       --- simpl in Hsetvariables. exists v. injection Hsetvariables as Hsetvariables.
           eapply eqb_eq in E. subst. rewrite <- Hsetvariables. auto.
       --- eapply eqb_neq in E. simpl in Hsetvariables. injection Hsetvariables as Hsetvariables.
           eapply IHt; eauto. simpl in H2. destruct H2.
           ---- destruct E. auto.
           ---- Search incl In. eapply incl_cons. apply H0.
                assert (incl [] t).
                { unfold incl. intros a. intros H5. unfold In in H5. destruct H5. } auto.
Qed.

Lemma aimp_to_functional_one_value : forall st0 X v a l (env : (total_map value))
(Hsetvariables : map (env) X = (map Number v)),
(length X = length v) ->
(incl (get_vars a) X) ->
(exists x0, eval (st0, (env)) (aimp_to_functional a) x0 =
     Some l) -> (exists w, [Number w] = l).
Proof.
  intros st0 X v a. revert X v. induction a.
  - intros X v l env Hsetvariables H0 H2 H1. simpl in H1. destruct H1.
    destruct x.
    -- simpl in H. discriminate.
    -- simpl in H. injection H as H. exists n. apply H.
  - intros X v l env Hsetvariables H0 H2 H1. simpl in H1. destruct H1.
    destruct x0.
    -- simpl in H. discriminate.
    -- simpl in H. injection H as H.
       simpl in H2. eapply needed_for_aimp; eauto.
  - intros X v l env Hsetvariables H0 H2 H1. simpl in H1. destruct H1; try discriminate.
    destruct x; try discriminate. simpl in H.
    destruct ( eval (st0, env)
        (aimp_to_functional a1) x); try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (n + n0). apply H.
  - intros X v l env Hsetvariables H0 H2 H1. simpl in H1. destruct H1; try discriminate.
    destruct x; try discriminate. simpl in H.
    destruct (eval (st0, env) (aimp_to_functional a1) x); try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate. destruct l0; try discriminate. destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (n - n0). apply H.
  - intros X v l env Hsetvariables H0 H2 H1. simpl in H1. destruct H1; try discriminate.
    destruct x; try discriminate. simpl in H.
    destruct (eval (st0, env) (aimp_to_functional a1) x); try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate. destruct l0; try discriminate. destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (n * n0). apply H.
Qed.

Lemma blank : forall st0 X v a (env : (total_map value))
(Hsetvariables : map (env) X = (map Number v)), (length X = length v) ->
       (exists x0, eval (st0, env)
       (aimp_to_functional a) x0 = Some []) -> False.
Proof.
  intros st0 X v a env. induction a.
  - intros Hsetvariables. intros H1. intros H2. destruct H2; try discriminate.
    destruct X as [| h t]; try discriminate.
    -- destruct x; try discriminate.
    -- destruct x; try discriminate.
  - intros Hsetvariables H1 H2. destruct H2; try discriminate.
    destruct X as [| h t]; try discriminate.
    -- destruct x0; try discriminate.
    -- destruct x0; try discriminate.
  - intros Hsetvariables H1 H2. destruct H2; try discriminate.
    destruct X as [| h t]; try discriminate.
    -- destruct x; try discriminate. simpl in H.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env) (aimp_to_functional a1) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
       destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
    -- destruct x; try discriminate.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env)
        (aimp_to_functional a1) x) eqn : Hx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
       destruct (eval
        (st0, env)
        (aimp_to_functional a2) x) eqn : Hxx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
  - intros Hsetvariables H1 H2. destruct H2; try discriminate.
    destruct X as [| h t]; try discriminate.
    -- destruct x; try discriminate. simpl in H.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env) (aimp_to_functional a1) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
       destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
    -- destruct x; try discriminate.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env)
        (aimp_to_functional a1) x) eqn : Hx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
       destruct (eval
        (st0, env)
        (aimp_to_functional a2) x) eqn : Hxx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
  - intros Hsetvariables H1 H2. destruct H2; try discriminate.
    destruct X as [| h t]; try discriminate.
    -- destruct x; try discriminate. simpl in H.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env) (aimp_to_functional a1) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
       destruct (eval (st0, env) (aimp_to_functional a2) x); try discriminate.
       destruct l; try discriminate.
       destruct v; try discriminate.
       destruct l; try discriminate.
    -- destruct x; try discriminate.
       destruct v as [| v vs]; try discriminate. simpl in H.
       destruct (eval (st0, env)
        (aimp_to_functional a1) x) eqn : Hx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
       destruct (eval
        (st0, env)
        (aimp_to_functional a2) x) eqn : Hxx; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct l; try discriminate.
Qed.

Lemma needed_for_environment_to_state : forall X v x st (env : (total_map value))
(Hsetvariables : map (env) X = (map Number v))
(Hst : map st X = v),
(length X = length v) ->
In x X ->
env x = compose Number st x.
Proof.
  intros X. induction X as [|h t].
  - intros v x st env Hsetvariables Hst H1 H2. Search In.
    eapply in_nil in H2. destruct H2.
  - intros v x st env Hsetvariables Hst H1 H2. Search In. eapply in_inv in H2.
    destruct H2.
    -- destruct v as [| v vs].
       --- simpl in H1. discriminate.
       --- simpl in Hsetvariables. injection Hsetvariables as Hsetvariables.
           simpl in Hst. injection Hst as Hst. rewrite <- ! H. rewrite Hsetvariables.
           Search compose. unfold compose. rewrite Hst. auto.
    -- destruct v as [| v vs].
       --- simpl in H1. discriminate.
       --- simpl in Hsetvariables. injection Hsetvariables as Hsetvariables.
           simpl in Hst. injection Hst as Hst.
           eapply IHt; eauto.
Qed.


Lemma environment_to_state : forall st0 X v a n w st (env : (total_map value))
(Hsetvariables : map env X = (map Number v))
(Hst : map st X = v),
(length X = length v) ->
(incl (get_vars a) X) ->
(eval (st0, env) (aimp_to_functional a) n = Some w) ->
(eval (st0, compose Number st) (aimp_to_functional a) n = Some w).
Proof.
  intros st0 X v a. revert X v. induction a.
  - intros. simpl.
    destruct n0; try discriminate. simpl in H1. simpl. apply H1.
  - intros X v n0 w st env Hsetvariables Hst H0 H1 H2. simpl.
    destruct n0; try discriminate. simpl in H2. simpl. simpl in H1. Search incl. symmetry in H2.
    rewrite H2. apply f_equal. symmetry. pose needed_for_environment_to_state.
    specialize e with (X:=X) (v:=v) (x:=x) (env:=env) (st:=st).
    specialize (e Hsetvariables). specialize (e Hst). specialize (e H0). 
    Search In incl. eapply incl_cons_inv in H1.  destruct H1. specialize (e H). rewrite e. reflexivity.
  - intros X v n0 w st env Hsetvariables Hst H0 H1 H2. simpl in H1. eapply incl_app_inv in H1.
    destruct H1.
    destruct n0; try discriminate. simpl. simpl in H2.
    destruct (eval (st0, env)
         (aimp_to_functional a1) n0) eqn : e; try discriminate.
    erewrite IHa1; eauto.
    destruct l eqn : L in H2; try discriminate. destruct v0 eqn : LL in H2; try discriminate.
    destruct l0 eqn : LLL in H2; try discriminate.
    destruct (eval (st0, env)
         (aimp_to_functional a2) n0) eqn : e2; try discriminate.
    erewrite IHa2; eauto.
    destruct l1 eqn : L1 in H2; try discriminate. destruct v1 eqn : LL1 in H2; try discriminate.
    destruct l2 eqn : LLL1 in H2; try discriminate. rewrite LL1 in L1. rewrite LLL1 in L1. subst. auto.
  - intros X v n0 w st env Hsetvariables Hst H0 H1 H2. simpl in H1. eapply incl_app_inv in H1.
    destruct H1.
    destruct n0; try discriminate. simpl. simpl in H2.
    destruct (eval (st0, env)
         (aimp_to_functional a1) n0) eqn : e; try discriminate.
    erewrite IHa1; eauto.
    destruct l eqn : L in H2; try discriminate. destruct v0 eqn : LL in H2; try discriminate.
    destruct l0 eqn : LLL in H2; try discriminate.
    destruct (eval (st0, env)
         (aimp_to_functional a2) n0) eqn : e2; try discriminate.
    erewrite IHa2; eauto.
    destruct l1 eqn : L1 in H2; try discriminate. destruct v1 eqn : LL1 in H2; try discriminate.
    destruct l2 eqn : LLL1 in H2; try discriminate. rewrite LL1 in L1. rewrite LLL1 in L1. subst. auto.
  - intros X v n0 w st env Hsetvariables Hst H0 H1 H2. simpl in H1. eapply incl_app_inv in H1.
    destruct H1.
    destruct n0; try discriminate. simpl. simpl in H2.
    destruct (eval (st0, env)
         (aimp_to_functional a1) n0) eqn : e; try discriminate.
    erewrite IHa1; eauto.
    destruct l eqn : L in H2; try discriminate. destruct v0 eqn : LL in H2; try discriminate.
    destruct l0 eqn : LLL in H2; try discriminate.
    destruct (eval (st0, env)
         (aimp_to_functional a2) n0) eqn : e2; try discriminate.
    erewrite IHa2; eauto.
    destruct l1 eqn : L1 in H2; try discriminate. destruct v1 eqn : LL1 in H2; try discriminate.
    destruct l2 eqn : LLL1 in H2; try discriminate. rewrite LL1 in L1. rewrite LLL1 in L1. subst. auto.
Qed.

Lemma singleton_incl_to_In : forall (x h : string) t, incl [x] (h::t) -> In x (h :: t).
Proof.
  intros. simpl. assert (In x [x]). { Search In. eapply in_eq. }
  eapply incl_cons_inv in H. destruct H. simpl in H. apply H.
Qed.

Lemma in_and_not_in_implies_not_equal : forall (X : list string) a x, ~ In a X -> In x X -> (a <> x).
Proof.
  induction X as [| h t].
  - intros. eapply in_nil in H; eauto.
  - intros. simpl in *. destruct H0.
    -- rewrite H0 in H. unfold not in H. unfold not. intros. apply H. left. symmetry. apply H1.
    -- apply IHt; auto.
Qed.

Lemma state_to_environment : forall x X Y st, NoDup X -> In x X -> 
make_conjunction X Y st
->
t_update_list empty_st X Y x = st x.
Proof.
  intros x X. revert x.
  induction X.
  - intros. eapply in_nil in H0. destruct H0.
  - intros. simpl in H1. destruct Y; try discriminate.
    -- destruct H1.
    -- destruct H1. simpl. destruct H0.
       --- rewrite H0. erewrite t_update_eq. rewrite <- H1. rewrite H0. auto.
       --- Search NoDup. eapply NoDup_cons_iff in H. destruct H.
           erewrite t_update_neq.
           ---- apply IHX; auto.
           ---- eapply in_and_not_in_implies_not_equal; auto.
                + apply H.
                + apply H0.
Qed.

Lemma needed_for_one_gen : forall a X v st, incl (get_vars a) X -> make_conjunction X v st -> NoDup X ->
aeval (t_update_list empty_st X v) a = aeval st a.
Proof.
  intros a.
  induction a.
  - intros. simpl. auto.
  - intros. simpl.
    destruct X as [| h t].
    -- simpl in *. Search incl. eapply NoDup_incl_length in H; auto.
       --- simpl in H. lia.
       --- eapply NoDup_cons; auto.
    -- simpl in *.
       destruct v as [| v vs].
       --- destruct H0.
       --- unfold "!->". eapply singleton_incl_to_In in H.
           simpl in H. destruct H.
           ---- rewrite H. erewrite equals_string. rewrite <- H. destruct H0. auto.
           ---- Search NoDup. eapply not_in in H1 as H2.
                destruct (h =? x) eqn : E.
                + eapply eqb_eq in E. rewrite E in H2. destruct H2. apply H.
                + destruct H0. eapply state_to_environment; eauto. Search NoDup. eapply NoDup_cons_iff in H1.
                  destruct H1. apply H4.
  - intros. simpl. simpl in H. Search incl. eapply incl_app_inv in H. destruct H. erewrite IHa2; auto.
  - intros. simpl. simpl in H. Search incl. eapply incl_app_inv in H. destruct H. erewrite IHa2; auto.
  - intros. simpl. simpl in H. Search incl. eapply incl_app_inv in H. destruct H. erewrite IHa2; auto.
Qed.

Lemma needed_for_one : forall x X v st, incl [x] X -> make_conjunction X v st -> NoDup X ->
aeval (t_update_list empty_st X v) x = aeval st x.
Proof.
  intros x X. revert x. induction X as [| h t].
  - intros x v st H1 H2 H3. pose incl_l_nil. specialize e with (A:=string) (l:=[x]). specialize (e H1). discriminate.
  - intros x v st H1 H2 H3. Search incl. unfold incl in H1. specialize H1 with (a:=x).
    assert (In x [x]).
    { unfold In. left. reflexivity. }
    specialize (H1 H). Search In. pose in_inv. specialize o with (A:=string) (a:=h) (b:=x) (l:=t).
    specialize (o H1). destruct o.
    -- destruct v as [| v vs]. 
       --- simpl in H2. destruct H2.
       --- simpl in H2. rewrite H0 in H2. simpl. rewrite H0. destruct H2. rewrite H2.
           unfold "!->". rewrite equals_string. reflexivity.
    -- destruct v as [| v vs].
       --- simpl in H2. destruct H2.
       --- simpl in H2. simpl. destruct H2. specialize IHt with (x:=x) (v:=vs) (st:=st).
           assert (incl [x] t).
           { unfold incl. intros a. intros eqn. simpl in eqn. destruct eqn. - rewrite <- H5. apply H0. - destruct H5. }
           specialize (IHt H5). specialize (IHt H4). Search NoDup. pose NoDup_cons_iff. specialize i with (A:=string) (a:=h) (l:=t).
           destruct i. specialize (H6 H3). destruct H6. specialize (IHt H8). simpl in IHt. rewrite <- IHt.
           unfold "!->". Search "=?".
           destruct (h =? x) eqn : E.
           ---- pose eqb_eq. specialize i with (n:=h) (m:=x). destruct i. specialize (H9 E). rewrite <- H9 in H0. elim H6. apply H0.
           ---- reflexivity.
Qed.

Lemma one : forall a X v st, incl (get_vars a) X -> make_conjunction X v st -> NoDup X ->
aeval (t_update_list empty_st X v) a = aeval st a.
Proof.
  intros a. induction a.
  - intros X v st H1 H2 H3. simpl. reflexivity.
  - intros X v st H1 H2 H3. apply needed_for_one.
    -- simpl. simpl in H1. apply H1.
    -- apply H2.
    -- apply H3.
  - intros X v st H1 H2 H3. simpl. simpl in H1. Search incl. pose incl_app_inv. specialize a with (A:=string) (l1:=get_vars a1)
    (l2:=get_vars a2) (m:=X). specialize (a H1). destruct a as [E1 E2].
    specialize IHa1 with (X:=X) (v:=v) (st:=st). specialize (IHa1 E1). specialize (IHa1 H2). specialize (IHa1 H3). rewrite IHa1.
    specialize IHa2 with (X:=X) (v:=v) (st:=st). specialize (IHa2 E2). specialize (IHa2 H2). specialize (IHa2 H3). rewrite IHa2.
    reflexivity.
  - intros X v st H1 H2 H3. simpl. simpl in H1. Search incl. pose incl_app_inv. specialize a with (A:=string) (l1:=get_vars a1)
    (l2:=get_vars a2) (m:=X). specialize (a H1). destruct a as [E1 E2].
    specialize IHa1 with (X:=X) (v:=v) (st:=st). specialize (IHa1 E1). specialize (IHa1 H2). specialize (IHa1 H3). rewrite IHa1.
    specialize IHa2 with (X:=X) (v:=v) (st:=st). specialize (IHa2 E2). specialize (IHa2 H2). specialize (IHa2 H3). rewrite IHa2.
    reflexivity.
  - intros X v st H1 H2 H3. simpl. simpl in H1. Search incl. pose incl_app_inv. specialize a with (A:=string) (l1:=get_vars a1)
    (l2:=get_vars a2) (m:=X). specialize (a H1). destruct a as [E1 E2].
    specialize IHa1 with (X:=X) (v:=v) (st:=st). specialize (IHa1 E1). specialize (IHa1 H2). specialize (IHa1 H3). rewrite IHa1.
    specialize IHa2 with (X:=X) (v:=v) (st:=st). specialize (IHa2 E2). specialize (IHa2 H2). specialize (IHa2 H3). rewrite IHa2.
    reflexivity.
Qed.

Lemma two : forall st0 X x a n v v' st, make_conjunction X v st -> 
eval (st0, x !-> Number (aeval st a); compose Number st) (Vars (map VariableToken X)) n = Some (map Number v') ->
NoDup X ->
make_conjunction X v' (x !-> aeval st a; st).
Proof.
  intros st0 X.
  induction X as [| x xs].
  - intros x a n v v' st H1 H2 H3.
    destruct v as [| v vs].
    -- destruct v' as [| v' vs'].
       --- simpl. auto.
       --- destruct n.
           ---- simpl in H2. discriminate.
           ---- simpl in H2. injection H2 as H2. discriminate.
    -- destruct v' as [| v' vs'].
       --- simpl. auto.
       --- destruct n.
           ---- simpl in H2. discriminate.
           ---- simpl in H2. injection H2 as H2. discriminate.
  - intros x0 a n v v' st H1 H2 H3.
    destruct v as [| v vs].
    -- destruct v' as [| v' vs']; try discriminate.
       --- destruct n.
           ---- simpl in H2. discriminate.
           ---- simpl in H2. injection H2 as H2. discriminate.
       --- destruct n; try discriminate. simpl in H2. simpl in H1. destruct H1.
    -- destruct v' as [| v' vs']; try discriminate.
       --- destruct n.
           ---- simpl in H2. discriminate.
           ---- simpl in H2. injection H2 as H2. discriminate.
       --- destruct n.
           ---- simpl in H2. discriminate.
           ---- simpl in H2. injection H2 as H2. simpl.
                split.
                + unfold "!->" in H2. unfold "!->".
                  destruct (x0 =? x) eqn : E.
                  ++ injection H2 as H2. apply H2.
                  ++ unfold compose in H2. injection H2 as H2. apply H2.
                + specialize IHxs with (x:=x0) (a:=a) (n:=S n) (v:=vs) (v':=vs') (st:=st).
                  simpl in H1. destruct H1 as [H1'1 H1'2]. specialize (IHxs H1'2). simpl in IHxs.
                  apply IHxs.
                  ++ apply f_equal. apply H.
                  ++ Search NoDup. pose NoDup_cons_iff. specialize i with (A:=string) (a:=x) (l:=xs).
                     destruct i. specialize (H0 H3). destruct H0. apply H4.
Qed.

Lemma needed_for_last_step : forall (env1 env2 : total_map value) x n xs, map env1 xs = map env2 xs ->
map (x !-> n; env1) xs = map (x !-> n; env2) xs.
Proof.
  intros env1 env2 x n xs. revert env1 env2 x n.
  induction xs as [| h t].
  - intros env1 env2 x n H1. simpl. reflexivity.
  - intros env1 env2 x n H1. simpl. simpl in H1. specialize IHt with (env1:=env1) (env2:=env2) (x:=x) (n:=n).
    injection H1 as H1. specialize (IHt H). rewrite IHt. unfold "!->".
    destruct (x =? h).
    -- reflexivity.
    -- rewrite H1. reflexivity.
Qed.

Lemma only_variables_reduction : forall st0 f x, map f x = map_over_tokens (st0, f) (map VariableToken x).
Proof.
  intros. revert f.
  induction x as [| x xs].
  - intros. simpl. auto.
  - intros. simpl. apply f_equal. apply IHxs.
Qed.

Lemma map_over_tokens_vars : forall env1 env2 X, map_over_tokens (env1, env2) (map VariableToken X) = map env2 X.
Proof.
  intros. revert env1 env2.
  induction X as [| x xs].
  - intros. simpl. auto.
  - intros. simpl. apply f_equal. apply IHxs.
Qed.

Lemma last_step : forall st0 x st a X x0 v (env : (total_map value * total_map value)), make_conjunction X v st ->
NoDup X ->
eval (st0, x !-> Number (aeval st a); compose Number st) (Vars (map VariableToken X)) x0 =
eval (st0, x !-> Number (aeval st a); t_update_list (snd env) X (map Number v)) (Vars (map VariableToken X)) x0.
Proof.
  intros st0 x st a X. revert x st a.
  induction X as [| x xs].
  - intros x st a x0 v H1.
    destruct v as [| v vs].
    -- simpl. simpl in H1.
       destruct x0.
       --- simpl. reflexivity.
       --- simpl. reflexivity.
    -- simpl. simpl in H1. destruct H1. intros. destruct H.
  - intros x0 st a x1 v env H1 H2.
    destruct v as [| v vs].
    -- simpl. simpl in H1. destruct H1.
    -- simpl in H1. destruct H1 as [H1'1 H1'2].
       destruct x1.
       --- simpl. reflexivity.
       --- simpl. apply f_equal.
           specialize IHxs with (x:=x0) (st:=st) (a:=a) (x0:=S x1) (v:=vs) (env:=env).
           specialize (IHxs H1'2). eapply NoDup_cons_iff in H2.  destruct H2.
           specialize (IHxs H0). simpl in IHxs. injection IHxs as IHxs.
           rewrite IHxs.
           unfold "!->".
           destruct (x0 =? x) eqn : E.
           ---- apply f_equal. erewrite ! map_over_tokens_vars. eapply needed_for_last_step.
                erewrite ! map_over_tokens_vars in IHxs.
                pose needed_for_last_step. unfold "!->" in e.
                specialize e with (env1:=t_update_list (snd env) xs (map Number vs))
                                  (env2:=(x !-> Number v; t_update_list (snd env) xs (map Number vs)))
                                  (x:=x0) (n:=Number (aeval st a)) (xs:=xs). unfold "!->" in e.
                pose unused_variable. unfold "!->" in e0. specialize e0 with (x:=x) (xs:=xs) (v:=Number v)
                (m:=t_update_list (snd env) xs (map Number vs)). symmetry. apply e0. apply H.
           ---- rewrite equals_string. unfold compose. rewrite H1'1. apply f_equal.
                pose needed_for_last_step. unfold "!->" in e.
                specialize e with (env1:=t_update_list (snd env) xs (map Number vs))
                                  (env2:=(x !-> Number v; t_update_list (snd env) xs (map Number vs)))
                                  (x:=x0) (n:=Number (aeval st a)) (xs:=xs). unfold "!->" in e.
                unfold empty_environment in e. simpl in e.
                erewrite <- only_variables_reduction. erewrite <- only_variables_reduction.
                apply e. pose unused_variable. unfold "!->" in e0. specialize e0 with (x:=x) (xs:=xs) (v:=Number v)
                (m:=t_update_list (snd env) xs (map Number vs)). symmetry. apply e0. apply H.
Qed.

Lemma extract_limits : forall st0 X c env x l, eval (st0, env) (extract_fun c X) x = Some l ->
                       (exists name args body rho, l = [Closure name args body rho]).
Proof.
  intros st0 X c. revert X.
  induction c.
  - intros X env x l H1. simpl in H1.
    destruct x; try discriminate. simpl in H1. exists None. exists (map VariableToken X). exists (Vars (map VariableToken X)). exists (st0, env).
    injection H1 as H1. rewrite H1. reflexivity.
  - intros X env x0 l H1. simpl in H1. destruct x0; try discriminate. simpl in H1.
    exists None. exists (map VariableToken X). exists (Let (VariableToken x) (aimp_to_functional a) (Vars (map VariableToken X))). exists (st0, env).
    injection H1 as H1. rewrite H1. auto.
  - intros X env x l H1. simpl in H1. destruct x; try discriminate. simpl in H1.
    exists None. exists (map VariableToken X). exists (Application (extract_fun c2 X ) ( Application (extract_fun c1 X)(Vars (map VariableToken X)) )). exists (st0, env).
    injection H1 as H1. rewrite H1. auto.
  - intros X env x l H1. simpl in H1. destruct x; try discriminate. simpl in H1.
    inversion H1; subst. exists None. exists (map VariableToken X).
    exists (If (bimp_to_functional b)
                 (Application (extract_fun c1 X)
                    (Vars (map VariableToken X)))
                 (Application (extract_fun c2 X)
                    (Vars (map VariableToken X)))) . exists (st0, env). auto.
    (*
    destruct (eval (st0, env) (bimp_to_functional b) x) eqn : E; try discriminate.
    destruct l0; try discriminate.
    destruct v; try discriminate.
    destruct b0; try discriminate.
    -- destruct l0; try discriminate. specialize IHc1 with (X:=X) (env:=env) (x:=x) (l:=l).
       specialize (IHc1 H1). apply IHc1.
    -- destruct l0; try discriminate. specialize IHc2 with (X:=X) (env:=env) (x:=x) (l:=l).
       specialize (IHc2 H1). apply IHc2. *)
  - intros X env x l H1. simpl in H1. destruct x; try discriminate. simpl in H1.
    injection H1 as H1. exists (Some (FunctionToken "Whilefun")). exists (map VariableToken X). exists (If (Application 
    ( Lambda (map VariableToken X)  (bimp_to_functional b) ) ( Vars (map VariableToken X) ))
           (Application ( Vars [FunctionToken "Whilefun"] ) (Application ( extract_fun c X ) ( Vars (map VariableToken X) ) )) 
           (Vars (map VariableToken X))). exists (st0, env). auto.
Qed.

Lemma reduce_set_variables : forall X v, NoDup X ->
      (length X = length v) ->
      map (snd (set_variables X (map Number v))) X = map Number v.
Proof.
  intros; apply step; auto.
Qed.

Lemma length_preserved : forall v, (length v = length (map Number v)).
Proof.
  intros v.
  induction v as [| v vs].
  - simpl. auto.
  - simpl. apply f_equal. rewrite IHvs. auto.
Qed.

Lemma get_number : forall X v h (env : (total_map value * total_map value)),
length X = length v ->
In h X ->
exists n,
t_update_list (snd env) X (map Number v) h = Number n.
Proof.
  intros X.
  induction X as [| x xs].
  - intros. Search In. eapply in_nil in H0. destruct H0.
  - intros.
    destruct v as [| v vs].
    -- simpl in H. lia.
    -- simpl. unfold "!->".
       destruct (x =? h) eqn : E.
       --- exists v. auto.
       --- simpl in H. injection H as H. Search In. eapply in_inv in H0.
           Search "=?". eapply eqb_neq in E. destruct H0.
           ---- destruct E. apply H0.
           ---- specialize IHxs with (v:=vs) (h:=h). specialize (IHxs env). specialize (IHxs H). specialize (IHxs H0).
                destruct IHxs. exists x0. apply H1.
Qed.

Lemma trivial_update : forall X v h x1 (env : (total_map value * total_map value)),
In h X ->
map (snd env) X = map Number v ->
t_update_list (snd env) X (map Number v) h = Number x1 ->
(snd env) h = Number x1.
Proof.
  intros X.
  induction X.
  - intros. simpl in *. destruct H.
  - intros. simpl in *.
    destruct (map Number v) eqn : E1; try discriminate.
    destruct H.
    -- subst. erewrite t_update_eq in H1. injection H0 as H0. subst. auto.
    -- injection H0 as H0. unfold "!->" in H1.
       destruct (a =? h) eqn : E in H1.
       --- subst. Search "=?". eapply eqb_eq in E. subst. auto.
       --- destruct v in E1; try discriminate. simpl in E1. injection E1 as E1.
           rewrite <- H3 in H1. rewrite <- H3 in H2. specialize IHX with (v:=v) (h:=h) (x1:=x1) (env:=env).
           specialize (IHX H). specialize (IHX H2). specialize (IHX H1). apply IHX.
Qed.

Lemma reduce_t_update : forall t x x0 (m n : total_map value),
map m t = map n t ->
map (x !-> x0; m) t = map (x !-> x0; n) t.
Proof.
  intros t.
  induction t.
  - intros. simpl in *. auto.
  - intros. simpl in *. injection H as H.
    destruct (x =? a) eqn : E.
    -- eapply eqb_eq in E. subst. erewrite ! t_update_eq. apply f_equal.
       eapply IHt. apply H0.
    -- eapply eqb_neq in E. erewrite ! t_update_neq; eauto. rewrite H. apply f_equal. apply IHt; eauto.
Qed.

Lemma redundant_update_prime : forall a X v (env : (total_map value * total_map value))
(Hsetvariables : map (snd env) X = v),
t_update_list (snd env) X v a = (snd env) a.
Proof.
  intros a X. revert a.
  induction X as [| h t].
  - intros. simpl. destruct v; eauto.
  - intros. simpl in *.
    destruct v as [| vh vt].
    -- auto.
    -- destruct (h =? a) eqn : E; try discriminate.
       --- eapply eqb_eq in E. subst. erewrite t_update_eq. injection Hsetvariables as Hsetvariables. auto.
       --- eapply eqb_neq in E. erewrite t_update_neq; eauto. eapply IHt. injection Hsetvariables as Hsetvariables.
           auto.
Qed.

Lemma redundant_update : forall X v (env : (total_map value * total_map value))
(Hsetvariables : map (snd env) X = v),
map (t_update_list (snd env) X v) X = map (snd env) X.
Proof.
  intros X.
  induction X as [| h t].
  - intros. simpl. auto.
  - intros. simpl in *.
    destruct v as [| vh vt].
    -- apply f_equal. auto.
    -- erewrite t_update_eq. injection Hsetvariables as Hsetvariables. rewrite <- Hsetvariables. apply f_equal.
       erewrite <- redundant_update_prime; eauto. erewrite t_update_same. eapply IHt; eauto.
Qed.

Lemma broken_t_update : forall h t v vs (env : (total_map value * total_map value)) (Hsetvariables : snd env h = Number v),
map (snd env) t = map Number vs ->
map
  (h !-> Number v;
   t_update_list (snd env) t (map Number vs)) t =
map
  (t_update_list (snd env) t (map Number vs)) t.
Proof.
  intros. rewrite <- Hsetvariables. erewrite <-redundant_update_prime.
  - instantiate (1:=(map Number vs)). instantiate (1:=t). erewrite t_update_same. auto.
  - auto.
Qed.

Lemma new_list : forall x x0 X v (env : (total_map value * total_map value)) (Hsetvariables : map (snd env) X = (map Number v)),
length X = length v ->
map (x !-> Number x0; t_update_list (snd env) X (map Number v)) X =
map (x !-> Number x0; (snd env)) X.
Proof.
  intros. revert Hsetvariables. revert x x0 v H.
  induction X as [| h t].
  - intros. simpl. auto.
  - intros.
    destruct v as [| v vs].
    -- simpl. auto.
    -- destruct (x =? h) eqn : E.
       --- simpl in *. injection Hsetvariables as Hsetvariables. Search "=?". eapply eqb_eq in E. subst.
           erewrite t_update_eq. erewrite t_update_eq. apply f_equal. Search t_update. erewrite t_update_shadow.
           eapply IHt; eauto.
       --- simpl in *. erewrite t_update_neq. 2 : {eapply eqb_neq in E. apply E. } erewrite t_update_eq.
           erewrite t_update_neq. 2 : {eapply eqb_neq in E. apply E. } injection Hsetvariables as Hsetvariables. rewrite Hsetvariables.
           apply f_equal. erewrite <- IHt; eauto. eapply reduce_t_update. eapply broken_t_update; eauto.
Qed.

Lemma incl_in_vars : forall x x0 X v s (env : (total_map value * total_map value)) 
(Hsetvariables : map (snd env) X = (map Number v)),
length X = length v ->
incl s X ->
exists v',
map (x !-> Number x0; snd env) s =
map Number v'.
Proof.
  intros. revert Hsetvariables. revert x x0 v s H H0.
  induction s as [| h t].
  - intros. simpl. exists []. auto.
  - intros. simpl. unfold "!->" in *.
    destruct (x =? h).
    -- specialize (IHt H). Search incl. eapply incl_cons_inv in H0. destruct H0.
       specialize (IHt H1). destruct IHt; eauto. exists (x0::x1). simpl. apply f_equal.
       apply H2.
    -- unfold set_variables in *. pose get_number as E. specialize E with (X:=X) (v:=v) (h:=h) (env:=env).
       specialize (E H). eapply incl_cons_inv in H0. destruct H0. specialize (E H0).
       destruct E. specialize (IHt H). specialize (IHt H1). destruct IHt; eauto.
       exists (x1::x2). simpl in H2. simpl. erewrite trivial_update; eauto.
       apply f_equal. simpl in H3. rewrite H3. simpl. auto.
Qed.

Lemma make_numbers : forall x x0 X v (env : (total_map value * total_map value)) (Hsetvariables : map (snd env) X = (map Number v)),
length X = length v ->
exists v',
map (x !-> Number x0; snd env) X = map Number v'.
Proof.
  intros. revert Hsetvariables. revert x x0 v H.
  induction X as [| h t] eqn : E1.
  - intros. simpl. exists []. auto.
  - intros.
    destruct v as [| hv vs] eqn : E2.
    -- simpl in H. lia.
    -- simpl. pose incl_in_vars as E. specialize E with (x:=x) (x0:=x0) (X:=(h::t)) (v:=(hv::vs)) (s:=t).
       pose incl_refl. specialize i with (A:=string) (l:=t). pose incl_tl.
       specialize i0 with (A:=string) (a:=h) (l:=t) (m:=t). specialize (i0 i). specialize E with (env:=env). 
       specialize (E Hsetvariables). specialize (E H).
       specialize (E i0). destruct E. simpl in H0. simpl in Hsetvariables.
       injection Hsetvariables as Hsetvariables. rewrite H0.
       unfold "!->".
       destruct (x =? h).
       --- exists (x0::x1). simpl. auto.
       --- rewrite Hsetvariables. exists (hv::x1). simpl. auto.
Qed.

Lemma create_new_number : forall x x0 X v (env : (total_map value * total_map value)) (Hsetvariables : map (snd env) X = (map Number v)),
length X = length v -> exists v',
map (x !-> Number x0; t_update_list (snd env) X (map Number v)) X = map Number v'.
Proof.
  intros. erewrite new_list; auto. eapply make_numbers; eauto.
Qed.

Lemma unneeded_function_env : forall env1 env2 X, map_over_tokens (env1, env2) (map VariableToken X) = map env2 X.
Proof.
  intros env1 env2 X. revert env1 env2.
  induction X as [|h t].
  - intros. simpl. auto.
  - intros. simpl. hnf. unfold snd. apply f_equal. apply IHt.
Qed.

Lemma snd_over_variables  : forall X v, length X = length v -> NoDup X ->
(map (snd (set_variables X (map Number v))) X) =
            (map_over_tokens (set_variables X (map Number v))
             (map VariableToken X)).
Proof.
  induction X as [|x xs].
  - intros. simpl. auto.
  - intros. destruct v as [|v vs].
    -- intros. simpl in H. lia.
    -- intros. unfold set_variables. simpl. apply f_equal. erewrite unneeded_function_env. auto.
Qed.


Lemma simpl_over_tokens : forall X v, length X = length v -> NoDup X ->
(map (snd (set_variables X (map Number v))) X) = (map Number v).
Proof.
  induction X as [| x xs].
  - intros. simpl.
    destruct v as [| v vs].
    -- simpl. auto.
    -- simpl in H. lia.
  - intros.
    destruct v as [| v vs].
    -- simpl in H. lia.
    -- simpl. unfold "!->". Search "=?". erewrite eqb_refl. apply f_equal.
       unfold set_variables in IHxs. pose unused_variable as Eq.
       specialize Eq with (v:=Number v) (m := t_update_list
       (fun x0 : string => FreeVariable (VariableToken x0)) xs
       (map Number vs)) (xs := xs) (x:=x). unfold "!->" in Eq.
       rewrite Eq.
       --- eapply IHxs.
           ---- simpl in H. lia.
           ---- Search NoDup. eapply NoDup_cons_iff in H0. destruct H0. auto.
       --- eapply NoDup_cons_iff in H0. destruct H0. auto.
Qed.

Lemma need_for_fst : forall (x y : total_map value), fst (x, y) = x.
Proof.
  simpl. intros. auto.
Qed.

Lemma need_for_snd : forall (x y : total_map value), snd (x, y) = y.
Proof.
  simpl. intros. auto.
Qed.

Lemma NoDup_injective_function : forall X, NoDup X -> NoDup (map VariableToken X).
Proof.
  intros. apply Injective_map_NoDup ; auto. unfold Injective. intros. inversion H0. auto.
Qed.

Lemma unused_function_env : forall X v, length X = length v -> NoDup X ->
map_over_tokens
       (token_update_list (set_variables X (map Number v))
          (map VariableToken X)
          (map_over_tokens (set_variables X (map Number v))
             (map VariableToken X))) (map VariableToken X) =
map
      (t_update_list (snd (set_variables X (map Number v))) X
         (map (snd (set_variables X (map Number v))) X)) X.
Proof.
  intros. erewrite <- snd_over_variables. 2: auto. 2: auto.  erewrite simpl_over_tokens. 2:auto. 2:auto.
  erewrite needed_for_reduce_again_token_version. Search NoDup.
  - erewrite needed_for_reduce_again.
    -- auto.
    -- Search length. erewrite map_length. auto.
    -- auto.
  - erewrite map_length. erewrite map_length. auto.
  - eapply NoDup_injective_function. auto.
Qed.

Lemma token_update_vars : forall (env : (total_map value * total_map value)) X v, token_update_list env (map VariableToken X) v = 
(fst env, t_update_list (snd env) X v).
Proof.
  intros env X. revert env.
  induction X as [| x xs].
  - intros. simpl.
    destruct v as [| v vs].
    -- destruct env. simpl. auto.
    -- destruct env. auto.
  - intros. simpl.
    destruct v as [| v vs].
    -- destruct env; auto.
    -- erewrite IHxs. simpl. auto.
Qed.

Lemma token_update_function : forall (env : (total_map value * total_map value)) X v, token_update_list env (map FunctionToken X) v =
(t_update_list (fst env) X v, snd env).
Proof.
  intros env X. revert env.
  induction X as [| x xs].
  - intros. simpl.
    destruct v as [| v vs].
    -- destruct env. simpl. auto.
    -- destruct env. auto.
  - intros. simpl.
    destruct v as [| v vs].
    -- destruct env; auto.
    -- erewrite IHxs. simpl. auto.
Qed.

Lemma equivalent_env_update : forall (v0 : total_map value) X, NoDup X ->
t_update_list v0 X (map v0 X) = v0.
Proof.
  intros v0 X. revert v0.
  induction X as [| x xs].
  - intros. simpl. auto.
  - intros. simpl. apply functional_extensionality.
    intros. unfold "!->".
    destruct (x =? x0) eqn : E.
    -- erewrite eqb_eq in E. subst. auto.
    -- eapply NoDup_cons_iff in H. destruct H. erewrite IHxs; eauto.
Qed.

Lemma equivalent_env_update_redux : forall (v0 : total_map value) X,
t_update_list v0 X (map v0 X) = v0.
Proof.
  intros v0 X. revert v0.
  induction X as [| x xs].
  - intros. simpl. auto.
  - intros. simpl. apply functional_extensionality.
    intros. unfold "!->".
    destruct (x =? x0) eqn : E.
    -- erewrite eqb_eq in E. subst. auto.
    -- erewrite IHxs; eauto.
Qed.

Lemma redundant_t_update_eval :  forall t v0 X f n l0,
NoDup X ->
eval (t, t_update_list v0 X (map v0 X)) f n = Some l0 -> 
eval (t, v0) f n = Some l0.
Proof.
  intros. erewrite equivalent_env_update in H0; eauto.
Qed.

Lemma extract_fun_same_lengths : forall c1 X x4 v n (env : (total_map value * total_map value))
       (Hlength : length X = length v) (HDup : NoDup X)
       (Hsetvariables : map (snd env) X = (map Number v)),
       eval (env) (Application ( extract_fun c1 X ) ( Vars (map VariableToken X) )) n =
       Some (map Number x4) -> length X = length x4.
Proof.
  intros c.
  induction c.
  - intros. destruct n; try discriminate. simpl in H.
    destruct n; try discriminate. simpl in H.
    destruct env. simpl in Hsetvariables. erewrite map_over_tokens_vars in H.
    erewrite token_update_vars in H. simpl in H. erewrite map_over_tokens_vars in H. injection H as H.
    erewrite needed_for_reduce_again in H; eauto.
    -- symmetry. erewrite <- map_length. instantiate (1:=Number). rewrite <- H. erewrite map_length. auto.
    -- erewrite map_length. auto.
  - intros. simpl in H. destruct n; try discriminate. simpl in H. destruct n; try discriminate. simpl in H.
    destruct env. simpl in *. erewrite map_over_tokens_vars in H. erewrite token_update_vars in H. simpl in H.
    destruct a.
    -- destruct n; try discriminate. simpl in H. injection H as H. erewrite map_over_tokens_vars in H.
       symmetry. erewrite <- map_length. instantiate (1:=Number). rewrite <- H.
       erewrite map_length. auto.
    -- destruct n; try discriminate. simpl in H. injection H as H. symmetry. erewrite <- map_length.
       instantiate (1:=Number). rewrite <- H. erewrite map_over_tokens_vars. erewrite map_length. auto.
    -- destruct (eval (t, t_update_list t0 X (map t0 X))
        (aimp_to_functional <{ a1 + a2 }>) n); try discriminate.
       destruct l.
       --- destruct n; try discriminate. simpl in H. injection H as H. erewrite map_over_tokens_vars in H.
           symmetry. erewrite <- map_length. instantiate (1:=Number). rewrite <- H. erewrite map_length. auto.
       ---
Admitted.

Lemma must_obtain_numbers : forall c X n l v env (Hsetvariables : map (snd env) X = (map Number v)),
NoDup X -> (length X = length v) ->
eval (env) (Application (extract_fun c X) (Vars (map VariableToken X))) n = Some l -> incl (get_variables c) X ->
                            (exists v', l = map Number v').
Proof.
  intros c.
  induction c.
  - intros X n l v env Hsetvariables H1 H2 H3 H4. simpl in H3. destruct n; try discriminate. simpl in H3.
    destruct n; try discriminate. simpl in H3. pose needed_for_reduce_again.
    injection H3 as H3. erewrite token_update_vars in H3. erewrite map_over_tokens_vars in H3. replace env with (fst env, snd env) in H3.
    2 : {symmetry. eapply decompose_prod. } erewrite map_over_tokens_vars in H3. rewrite Hsetvariables in H3. simpl in H3.
    erewrite e in H3; eauto. erewrite map_length. apply H2.
  - Search aimp_to_functional. intros X n l v env Hsetvariables H1 H2 H3 H4. simpl in H3. destruct n; try discriminate. simpl in H3.
    destruct n; try discriminate. simpl in H3.
    erewrite token_update_vars in H3. destruct env. simpl in *. erewrite map_over_tokens_vars in H3.
    destruct ( eval (t, t_update_list v0 X (map v0 X))
         (aimp_to_functional a) n) eqn : Esimpl; try discriminate. edestruct aimp_to_functional_one_value; eauto.
    { instantiate (1:=a). eapply incl_cons_inv; eauto. }
    { instantiate (1:=l0). instantiate (1:=t). simpl. exists n. erewrite redundant_t_update_eval; eauto. }
    destruct n; try discriminate. simpl in H3. injection H3 as H3. rewrite <- H in H3. erewrite map_over_tokens_vars in H3.
    rewrite Hsetvariables in H3. pose create_new_number as E. specialize E with (x:=x) (x0:=x0) (X:=X) (v:=v) (env:=(v0,v0)).
    simpl in E. specialize (E Hsetvariables). specialize (E H2). destruct E. exists x1. rewrite H3 in H0. auto.
  - intros X n l v env Hsetvariables H1 H2 H3 H4. simpl in H3. destruct n; try discriminate. simpl in H3.
    destruct ( eval env
           (Lambda (map VariableToken X)
              (Application (extract_fun c2 X)
                 (Application (extract_fun c1 X) (Vars (map VariableToken X))))) n) eqn : Hc2; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate. 
    destruct (eval (env) (Vars (map VariableToken X)) n) eqn : Hx; try discriminate. 
    destruct n; try discriminate. simpl in Hc2. inversion Hc2. subst. simpl in H3. erewrite token_update_vars in H3; auto.
    destruct (eval
         (fst (env0),
         t_update_list (snd (env0)) X l0)
         (extract_fun c2 X) n) eqn : Hc2'; try discriminate. simpl in Hx. replace env0 with ((fst env0, snd env0)) in Hx; eauto.
    2 : { erewrite decompose_prod. auto. } erewrite map_over_tokens_vars in Hx. injection Hx as Hx. setoid_rewrite Hsetvariables in Hx.
    rewrite <- Hx in Hc2'. rewrite <- Hsetvariables in Hc2'. eapply redundant_t_update_eval in Hc2'; eauto.
    erewrite <- decompose_prod in Hc2'.
    destruct l1; try discriminate.
    destruct v0; try discriminate.
    destruct l1; try discriminate.
    destruct (eval
           (pair (fst (env0))
              (t_update_list (snd (env0)) X
                 l0))
           (Application (extract_fun c1 X)
              (Vars (map VariableToken X))) n) eqn : Hc1; try discriminate.
    specialize IHc1 with (X:=X) (n:=n) (l:=l1) (v:=v) (env:=(fst env0, t_update_list (snd env0) X l0)).
    simpl in IHc1. erewrite needed_for_reduce_again in IHc1; eauto.
    2:{ rewrite <- Hx. erewrite map_length. apply H2. } symmetry in Hx. specialize (IHc1 Hx).
    specialize (IHc1 H1). specialize (IHc1 H2). specialize (IHc1 Hc1). simpl in H4. eapply incl_app_inv in H4.
    destruct H4. specialize (IHc1 H). destruct IHc1. rewrite H4 in H3.
    eapply IHc2.
    -- instantiate (1:=x). instantiate (1:=X). instantiate (1:=(fst env, t_update_list (snd env) X (map Number x))).
       simpl. erewrite needed_for_reduce_again; eauto. erewrite map_length. eapply extract_fun_same_lengths; auto.
       3:{ rewrite <- H4. apply Hc1. }
       2:{ simpl. rewrite Hx. rewrite <- Hsetvariables. erewrite needed_for_reduce_again; eauto. erewrite map_length.
           auto. } apply H2.
    -- apply H1.
    -- eapply extract_fun_same_lengths; auto.
       3:{ rewrite <- H4. apply Hc1. }
       2:{ simpl. rewrite Hx. rewrite <- Hsetvariables. erewrite needed_for_reduce_again; eauto. erewrite map_length.
           auto. } apply H2.
    -- instantiate (1:=(S n)). simpl.
    Admitted.

Lemma plus_one_fuel : forall env f x l, eval env f x = Some l -> eval env f (S x) = Some l.
Proof.
  intros env f x. revert env f.
  induction x.
  - destruct f; auto; discriminate.
  - destruct f.
    -- intros. simpl in H. simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H. remember (S x) as n.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       remember (S x) as m.
       simpl. erewrite IHx. 2 : apply E1.
       simpl. erewrite IHx. 2 : apply E2.
       simpl. auto.
    -- intros. simpl in H. remember (S x) as n.
       simpl.
       destruct (eval env f x) eqn : E; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct b; try discriminate.
       --- destruct l0; try discriminate. rewrite <- H.
           erewrite IHx. 2 : apply E. simpl. auto.
       --- destruct l0; try discriminate. rewrite <- H.
           erewrite IHx. 2 : apply E. simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct b; try discriminate.
       --- destruct l0; try discriminate.
           destruct (eval env f2 x) eqn : E2; try discriminate.
           destruct l0; try discriminate.
           destruct v; try discriminate.
           destruct b; try discriminate.
           ---- destruct l0; try discriminate. remember (S x) as n. simpl.
                erewrite IHx. 2 : apply E1. simpl. erewrite IHx. 2 : apply E2. simpl. auto.
           ---- destruct l0; try discriminate. remember (S x) as n. simpl.
                erewrite IHx. 2 : apply E1. simpl. erewrite IHx. 2 : apply E2. simpl. auto.
       --- destruct l0; try discriminate.
           destruct (eval env f2 x) eqn : E2; try discriminate.
           destruct l0; try discriminate.
           destruct v; try discriminate.
           destruct b; try discriminate.
           ---- destruct l0; try discriminate. remember (S x) as n. simpl.
                erewrite IHx. 2 : apply E1. simpl. erewrite IHx. 2 : apply E2. simpl. auto.
           ---- destruct l0; try discriminate. remember (S x) as n. simpl.
                erewrite IHx. 2 : apply E1. simpl. erewrite IHx. 2 : apply E2. simpl. auto.
    -- intros. simpl in H. remember (S x) as n. simpl. auto.
    -- intros. simpl in H. remember (S x) as n. simpl.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       --- erewrite IHx. 2 : apply E1. simpl. auto.
       --- erewrite IHx. 2 : apply E1. simpl. auto.
    -- intros. simpl in H. remember (S x) as n.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct b; try discriminate.
       --- destruct l0; try discriminate. simpl.
           erewrite IHx. 2 : apply E1. simpl. auto.
       --- destruct l0; try discriminate. simpl.
           erewrite IHx. 2 : apply E1. simpl. auto.
    -- intros. simpl in H. remember (S x) as n. simpl. auto.
    -- intros. simpl in H.
       destruct (eval env f1 x) eqn : E1; try discriminate.
       destruct l0; try discriminate.
       destruct v; try discriminate.
       destruct l0; try discriminate.
       destruct (eval env f2 x) eqn : E2; try discriminate.
       destruct name; try discriminate.
       --- remember (S x) as n. simpl. erewrite IHx. 2 : apply E1.
           simpl. erewrite IHx. 2 : apply E2. apply IHx. auto.
       --- remember (S x) as n. simpl. erewrite IHx. 2 : apply E1.
           simpl. erewrite IHx. 2 : apply E2. apply IHx. auto.
    -- intros. simpl. simpl in H. auto.
Qed.

Lemma redux : forall (d1 d2 : total_map value) b v x0, length b = length v ->
In x0 b -> t_update_list d1 b v x0 = t_update_list d2 b v x0.
Proof.
  intros d1 d2 b. revert d1 d2.
  induction b.
  - intros. Search length. simpl in H. Search length. destruct H0.
  - intros. simpl.
    destruct v eqn : V.
    -- subst. simpl in H. discriminate.
    -- subst. simpl in H. unfold "!->".
       destruct (a =? x0) eqn : E.
       --- auto.
       --- erewrite IHb.
           ---- auto.
           ---- auto.
           ---- Search In. eapply in_inv in H0. destruct H0.
                + Search "=?". apply eqb_neq in E. destruct E. auto.
                + auto.
Qed.

Lemma unused_env : forall b v x (d1 r2 : total_map value), length b = length v -> In x b ->
t_update_list d1 b v x =
t_update_list r2 b v x.
Proof.
  intros b.
  induction b as [| h t].
  - intros. Search In. pose in_nil as E. specialize E with (a:=x). unfold not in E.
    specialize (E H0). destruct E.
  - intros.
    destruct v as [| v vs].
    -- simpl. simpl in H. lia.
    -- simpl. unfold "!->". simpl in H0.
       destruct (h =? x) eqn : E.
       --- auto.
       --- destruct H0; auto. Search "=?". erewrite eqb_neq in E. destruct E. apply H0.
Qed.

Lemma unused_env_list : forall b v (d1 r2 : total_map value), length b = length v ->
map (fun x' : string => t_update_list d1 b v x') b =
map (fun x' : string => t_update_list r2 b v x') b.
Proof.
  intro b.
  induction b as [| h t].
  - intros. simpl. auto.
  - intros.
    destruct v as [| v vs].
    -- simpl in H. lia.
    -- simpl in H. simpl. unfold "!->". erewrite equals_string. apply f_equal.
       pose needed_for_last_step as E. unfold "!->" in E.
       specialize E with (env1 := fun x'=>t_update_list d1 t vs x') (env2 := fun x'=>t_update_list r2 t vs x').
       specialize E with (x:=h) (n:=v) (xs:=t). simpl in E.
       apply E. eapply IHt; auto.
Qed.

Lemma added_map : forall x r b (env1 env2 : total_map value),
map (fun x' : string => env1 x') b =
map (fun x' : string => env2 x') b ->
map
  (fun x' : string =>
   if x =? x' then r else env1 x') b =
map
  (fun x' : string =>
   if x =? x' then r else env2 x') b.
Proof.
  intros x r b. revert x r.
  induction b as [| h t].
  - intros. simpl. auto.
  - intros. simpl. simpl in H. injection H as H. rewrite H. apply f_equal.
    apply IHt. apply H0.
Qed.

Lemma aimp_one_value : forall st0 env b v a n l (Hsetvariables : map env b = v),
eval (st0, env) (aimp_to_functional a) n = Some l -> (exists v, l = [v]).
Proof.
  intros st0 env b v a. revert env b v.
  induction a.
  - intros. simpl in *. destruct n0; try discriminate. simpl in H. injection H as H. exists (Number n). auto.
  - intros. simpl in *. destruct n; try discriminate. simpl in H. injection H as H.
    exists (env x). auto.
  - intros. simpl in H. destruct n; try discriminate. simpl in H.
    destruct (eval (st0, env) (aimp_to_functional a1) n) eqn : A1; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) n) eqn : A2; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (Number (n0 + n1)). auto.
  - intros. simpl in H. destruct n; try discriminate. simpl in H.
    destruct (eval (st0, env) (aimp_to_functional a1) n) eqn : A1; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) n) eqn : A2; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (Number (n0 - n1)). auto.
  - intros. simpl in H. destruct n; try discriminate. simpl in H.
    destruct (eval (st0, env) (aimp_to_functional a1) n) eqn : A1; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate.
    destruct (eval (st0, env) (aimp_to_functional a2) n) eqn : A2; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate. injection H as H. exists (Number (n0 * n1)). auto.
Qed.

Lemma same_map_update : forall x x0 x2 (env1 env2 : total_map value) b, In x b ->
map (x !-> x0; env1) b = map (x !-> x2; env2) b ->
x0 = x2.
Proof.
  intros x x0 x2 env1 env2 b. revert x x0 x2 env1 env2.
  induction b as [| h t].
  - intros. destruct H.
  - intros. simpl in H0. inversion H0; subst.
    destruct H.
    -- unfold "!->" in H2. symmetry in H. eapply eqb_eq in H. rewrite H in H2. auto.
    -- eapply IHt; auto. apply H. apply H3.
Qed.

Lemma needed_for_closed_env : forall st0 st1 d1 r2 b v x a n, incl (x::get_vars a) b -> length b = length v ->
eval (st0, t_update_list d1 b v) (Let (VariableToken x) (aimp_to_functional a) (Vars (map VariableToken b))) (S n) =
eval (st1, t_update_list r2 b v) (Let (VariableToken x) (aimp_to_functional a) (Vars (map VariableToken b))) (S n).
Proof.
  intros st0 st1 d1 r2 b v x a. revert d1 r2 b v x.
  induction a.
  - intros. simpl.
    destruct n0; try discriminate.
    -- simpl. auto.
    -- simpl. apply f_equal. unfold "!->". pose needed_for_last_step as E.
       unfold "!->" in E.
       specialize E with (env1:=fun x'=>t_update_list d1 b v x') (env2:=fun x'=>t_update_list r2 b v x')
       (x:=x) (n:=Number n) (xs:=b). simpl in E. erewrite map_over_tokens_vars. rewrite map_over_tokens_vars. apply E. apply unused_env_list; auto.
  - intros. simpl.
    destruct n; try discriminate.
    -- simpl. auto.
    -- simpl. apply f_equal. erewrite unused_env; auto.
       --- instantiate (1:=r2). unfold "!->". erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply added_map. eapply unused_env_list; auto.
       --- Search In. eapply incl_cons_inv in H. destruct H. simpl in H1. Search In.
           eapply incl_cons_inv in H1. destruct H1. auto.
  - intros. simpl.
    destruct n; auto.
    simpl. simpl in *.
    destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a1) n) eqn : Hd1a1; auto.
    -- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1; eauto.
                        eapply aimp_one_value in Hd1a2; eauto.
                        eapply aimp_one_value in Hr2a1; eauto.
                        eapply aimp_one_value in Hr2a2; eauto.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1. destruct Hr2a2.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                        simpl in IHa1. injection IHa1 as IHa1. erewrite map_over_tokens_vars in IHa1. 
                        erewrite map_over_tokens_vars in IHa1. eapply same_map_update in IHa1; eauto.
                        subst. simpl in IHa2. injection IHa2 as IHa2.
                        erewrite map_over_tokens_vars in IHa2. erewrite map_over_tokens_vars in IHa2.
                        eapply same_map_update in IHa2; auto.
                        subst.
                        destruct (  match x2 with
                                    | Number m =>
                                      match x3 with
                                      | Number l => Some [Number (m + l)]
                                      | _ => None
                                      end
                                    | _ => None
                                    end); auto. apply f_equal.
                        destruct l as [| l ls].
                        ++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply unused_env_list. auto.
                        ++ destruct ls; auto.
                           +++ Search map. erewrite map_over_tokens_vars. erewrite map_over_tokens_vars.
                               eapply needed_for_last_step. eapply unused_env_list. auto.
                           +++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars.
                               eapply needed_for_last_step. eapply unused_env_list. eauto.
                      + simpl in H. Search incl. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1; eauto.
                        eapply aimp_one_value in Hd1a2; eauto.
                        eapply aimp_one_value in Hr2a1; eauto.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                ----- (*simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2. destruct n; try discriminate. subst. rewrite Hr2a2 in IHa2.
                        simpl in IHa2. discriminate.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2.
                        destruct n; try discriminate. simpl in IHa1. injection IHa1 as IHa1.
                        destruct l; auto.
                        ++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                        ++ destruct v0; auto.
                           +++ destruct l; auto.
                               ++++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                               ++++ destruct l0; auto. destruct v1; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                ----- simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
       --- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
  - intros. simpl.
    destruct n; try discriminate.
    -- simpl. auto.
    -- simpl. simpl in *.
       destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a1) n) eqn : Hd1a1; auto.
       --- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1.
                        eapply aimp_one_value in Hd1a2.
                        eapply aimp_one_value in Hr2a1.
                        eapply aimp_one_value in Hr2a2.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1. destruct Hr2a2.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                        simpl in IHa1. injection IHa1 as IHa1. erewrite map_over_tokens_vars in IHa1. erewrite map_over_tokens_vars in IHa1.
                        eapply same_map_update in IHa1; auto.
                        subst. simpl in IHa2. injection IHa2 as IHa2. erewrite map_over_tokens_vars in IHa2. erewrite map_over_tokens_vars in IHa2.
                        eapply same_map_update in IHa2; auto.
                        subst.
                        destruct (  match x2 with
                                    | Number m =>
                                      match x3 with
                                      | Number l => Some [Number (m - l)]
                                      | _ => None
                                      end
                                    | _ => None
                                    end); auto. apply f_equal.
                        destruct l as [| l ls].
                        ++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply unused_env_list. auto.
                        ++ destruct ls; auto.
                           +++ Search map. erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply needed_for_last_step. eapply unused_env_list. auto.
                           +++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply needed_for_last_step. eapply unused_env_list. auto.
                      + simpl in H. Search incl. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1.
                        eapply aimp_one_value in Hd1a2.
                        eapply aimp_one_value in Hr2a1.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                ----- simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2. destruct n; try discriminate. subst. rewrite Hr2a2 in IHa2.
                        simpl in IHa2. discriminate.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2.
                        destruct n; try discriminate. simpl in IHa1. injection IHa1 as IHa1.
                        destruct l; auto.
                        ++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                        ++ destruct v0; auto.
                           +++ destruct l; auto.
                               ++++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                               ++++ destruct l0; auto. destruct v1; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                ----- simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
       --- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
  - intros. simpl.
    destruct n; try discriminate.
    -- simpl. auto.
    -- simpl. simpl in *.
       destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a1) n) eqn : Hd1a1; auto.
       --- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1.
                        eapply aimp_one_value in Hd1a2.
                        eapply aimp_one_value in Hr2a1.
                        eapply aimp_one_value in Hr2a2.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1. destruct Hr2a2.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                        simpl in IHa1. injection IHa1 as IHa1. erewrite map_over_tokens_vars in IHa1. erewrite map_over_tokens_vars in IHa1.
                        eapply same_map_update in IHa1; auto.
                        subst. simpl in IHa2. injection IHa2 as IHa2. erewrite map_over_tokens_vars in IHa2.
                        erewrite map_over_tokens_vars in IHa2.
                        eapply same_map_update in IHa2; auto.
                        subst.
                        destruct (  match x2 with
                                    | Number m =>
                                      match x3 with
                                      | Number l => Some [Number (m * l)]
                                      | _ => None
                                      end
                                    | _ => None
                                    end); auto. apply f_equal.
                        destruct l as [| l ls].
                        ++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply unused_env_list. auto.
                        ++ destruct ls; auto.
                           +++ Search map. erewrite map_over_tokens_vars. erewrite map_over_tokens_vars.
                               eapply needed_for_last_step. eapply unused_env_list. auto.
                           +++ erewrite map_over_tokens_vars. erewrite map_over_tokens_vars. eapply needed_for_last_step. eapply unused_env_list. auto.
                      + simpl in H. Search incl. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                        rewrite Hd1a2 in IHa2. rewrite Hr2a2 in IHa2.
                        assert (L := Hd1a1).
                        assert (L0 := Hd1a2).
                        assert (L1 := Hr2a1).
                        assert (L2 := Hr2a2).
                        eapply aimp_one_value in Hd1a1.
                        eapply aimp_one_value in Hd1a2.
                        eapply aimp_one_value in Hr2a1.
                        destruct Hd1a1. destruct Hd1a2. destruct Hr2a1.
                        eapply incl_cons_inv in H. destruct H.
                        eapply incl_cons_inv in H'. destruct H'.
                        subst. destruct n; try discriminate.
                ----- simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1.
                ----- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a2) n) eqn : Hr2a2.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2. destruct n; try discriminate. subst. rewrite Hr2a2 in IHa2.
                        simpl in IHa2. discriminate.
                      + simpl in H. eapply incl_cons_inv in H. destruct H. 
                        eapply incl_app_inv in H1. destruct H1.
                        assert (H' := H). eapply incl_cons in H.
                        2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                        specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                        specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                        rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                        rewrite Hd1a2 in IHa2.
                        destruct n; try discriminate. simpl in IHa1. injection IHa1 as IHa1.
                        destruct l; auto.
                        ++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                        ++ destruct v0; auto.
                           +++ destruct l; auto.
                               ++++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                               ++++ destruct l0; auto. destruct v1; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                           +++ destruct l0; auto. destruct v0; auto. destruct l0; auto.
                ----- simpl in H. eapply incl_cons_inv in H. destruct H. 
                      eapply incl_app_inv in H1. destruct H1.
                      assert (H' := H). eapply incl_cons in H.
                      2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                      specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                      specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                      rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1.
                      rewrite Hd1a2 in IHa2. destruct n; try discriminate.
       --- destruct (eval (st0, t_update_list d1 b v) (aimp_to_functional a2) n) eqn : Hd1a2; auto.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
           ---- destruct (eval (st1, t_update_list r2 b v) (aimp_to_functional a1) n) eqn : Hr2a1; auto.
                simpl in H. eapply incl_cons_inv in H. destruct H. 
                eapply incl_app_inv in H1. destruct H1.
                assert (H' := H). eapply incl_cons in H.
                2 : apply H1. eapply incl_cons in H'. 2 : apply H2.
                specialize IHa1 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize IHa2 with (d1:=d1) (r2:=r2) (b:=b) (v:=v) (x:=x) (n:=n).
                specialize (IHa1 H). specialize (IHa2 H'). specialize (IHa1 H0). specialize (IHa2 H0).
                rewrite Hd1a1 in IHa1. rewrite Hr2a1 in IHa1. 
                rewrite Hd1a2 in IHa2. destruct n; try discriminate.
Qed.*)
Admitted.

Lemma element_of_implies_In : forall x xs, element_of x xs = true -> In x xs.
Proof.
  intros x xs. revert x.
  induction xs as [| h t].
  - intros. simpl in H. discriminate.
  - intros. Search In. assert (In x (h :: t) = In x ([h] ++ t)). { simpl. auto. }
    rewrite H0. Search In. eapply in_or_app.
    simpl in H.
    destruct (h =? x) eqn : E; try discriminate.
    -- Search In. left. Search "=?". eapply eqb_eq in E. rewrite E. Search In.
       eapply in_eq.
    -- right. apply IHt. apply H.
Qed.

Lemma remove_dup_incl : forall X, incl (remove_dup X) X.
Proof.
  induction X as [| x xs].
  - simpl. Search incl. eapply incl_nil_l.
  - simpl. destruct (element_of x (remove_dup xs)) eqn : E.
    -- eapply element_of_implies_In in E. Search incl. eapply incl_tl. apply IHxs.
    -- Search incl. eapply incl_cons.
       --- Search In. eapply in_eq.
       --- Search incl. eapply incl_tl. apply IHxs.
Qed.

Lemma remove_dup_equals_incl : forall a X, incl (remove_dup a) X <-> incl a X.
Proof.
  split.
+
  induction a as [| h t].
  - intros. simpl in *. auto.
  - intros. Search incl. eapply incl_cons.
    -- unfold remove_dup in H. destruct (element_of h
          ((fix remove_dup (l : list string) : list string :=
              match l with
              | [] => []
              | x :: xs =>
                  if element_of x (remove_dup xs)
                  then remove_dup xs
                  else x :: remove_dup xs
              end) t)) eqn : E.
        --- fold remove_dup in *. eapply element_of_implies_In in E. Search incl.
            assert (incl [h] (remove_dup t)). { Search In. eapply incl_cons. - apply E. - Search incl. apply incl_nil_l. }
            assert (incl [h] X -> In h X).
            { intros. Search incl. destruct X as [| x xs]. - Search incl. eapply incl_l_nil in H1. discriminate.
              - eapply singleton_incl_to_In in H1. apply H1. }
            apply H1. Search incl. eapply incl_tran.
            ---- apply H0.
            ---- apply H.
        --- fold remove_dup in *. Search incl. eapply incl_cons_inv in H. destruct H. apply H.
    -- apply IHt. unfold remove_dup in *.
       destruct (element_of h
          ((fix remove_dup (l : list string) : list string :=
              match l with
              | [] => []
              | x :: xs =>
                  if element_of x (remove_dup xs)
                  then remove_dup xs
                  else x :: remove_dup xs
              end) t)) eqn : E.
        ---  apply H.
        --- fold remove_dup in *. Search incl. eapply incl_cons_inv in H. destruct H. apply H0.
+ induction a as [| h t].
  - intros. simpl in *. auto.
  - intros. simpl in *.
    destruct (element_of h (remove_dup t)).
    -- apply IHt. eapply incl_cons_inv in H. destruct H. auto.
    -- eapply incl_cons_inv in H. destruct H. Search incl. eapply incl_cons.
       --- apply H.
       --- apply IHt. apply H0.
Qed.

Lemma incl_equals : forall c X, incl (get_variables c) X <-> incl (variable_extraction c) X.
Proof.
  split.
+
  induction c.
  - intros. simpl in *. unfold variable_extraction. simpl. auto.
  - intros. simpl in *. unfold variable_extraction. simpl.
    destruct (element_of x (remove_dup (get_vars a))) eqn : E.
    -- eapply incl_cons_inv in H. destruct H. eapply remove_dup_equals_incl. apply H0.
    -- eapply incl_cons_inv in H. destruct H. Search incl. eapply incl_cons; auto.
        eapply remove_dup_equals_incl. auto.
  - intros. simpl in *. unfold variable_extraction. simpl. eapply remove_dup_equals_incl. apply H.
  - intros. simpl in *. unfold variable_extraction. simpl. eapply remove_dup_equals_incl. auto.
  - intros. simpl in *. unfold variable_extraction. simpl. eapply remove_dup_equals_incl. auto.
+
  induction c.
  - intros. simpl in *. unfold variable_extraction in *. simpl in *. apply H.
  - intros. simpl in *. unfold variable_extraction in *. simpl in *.
    destruct (element_of x (remove_dup (get_vars a))) eqn : E.
    -- eapply element_of_implies_In in E. Search incl. eapply incl_cons.
       --- Search In.
           destruct X as [| h t].
           ---- Search incl. eapply incl_l_nil in H. rewrite H in E. Search In. pose in_nil.
                specialize n with (A:=string) (a:=x). auto.
           ---- Search In. eapply singleton_incl_to_In. Search incl. eapply incl_tran. 2:apply H.
                Search In. eapply incl_cons in E. apply E. Search incl. apply incl_nil_l.
       --- eapply remove_dup_equals_incl. apply H.
    -- Search incl. eapply incl_cons_inv in H. destruct H. eapply incl_cons; auto. eapply remove_dup_equals_incl.
       apply H0.
  - intros. simpl in *. Search incl.
    unfold variable_extraction in H. simpl in H. erewrite remove_dup_equals_incl in H. apply H.
  - intros. simpl in *. Search incl.
    unfold variable_extraction in H. simpl in H. erewrite remove_dup_equals_incl in H. apply H.
  - intros. simpl in *. Search incl.
    unfold variable_extraction in H. simpl in H. erewrite remove_dup_equals_incl in H. apply H.
Qed.

Lemma t_update_overwrite : forall (d1 r1 : total_map value) b v h, In h b -> length b = length v -> NoDup b ->
t_update_list d1 b v h =
t_update_list r1 b v h.
Proof.
  intros. revert d1 r1 v h H H0 H1.
  induction b as [| h t].
  - intros. Search In. eapply in_nil in H. destruct H.
  - intros. simpl.
    destruct v as [| v vs].
    -- simpl in H0. lia.
    -- simpl in H. destruct H.
       --- rewrite H. erewrite t_update_eq. erewrite t_update_eq. auto.
       --- Search NoDup. eapply not_in in H1 as H2. erewrite ! t_update_neq.
           ---- apply IHt; auto. Search NoDup. eapply NoDup_cons_iff in H1.
                destruct H1. apply H3.
           ---- eapply in_and_not_in_implies_not_equal; auto. apply H2. apply H.
           ---- eapply in_and_not_in_implies_not_equal; auto. apply H2. apply H.
Qed.

Lemma overwrite_env_vars : forall st0 d1 r1 b v X n, incl X b -> length b = length v -> NoDup b ->
eval (st0, t_update_list d1 b v) (Vars (map VariableToken X)) n =
eval (st0, t_update_list r1 b v) (Vars (map VariableToken X)) n.
Proof.
  intros. revert d1 r1 b v n H H0 H1.
  induction X as [| h t].
  - intros. simpl. destruct n.
    -- simpl. auto.
    -- simpl. auto.
  - intros. simpl. destruct n.
    -- simpl. auto.
    -- simpl. apply f_equal. eapply incl_cons_inv in H as H2. destruct H2.
       erewrite t_update_overwrite; auto. apply f_equal.
       specialize IHt with (n:=S n). simpl in IHt. assert (Some
        (map_over_tokens (st0, t_update_list d1 b v)
           (map VariableToken t)) =
      Some
        (map_over_tokens (st0, t_update_list r1 b v)
           (map VariableToken t)) -> map_over_tokens (st0, t_update_list d1 b v)
  (map VariableToken t) =
map_over_tokens (st0, t_update_list r1 b v)
  (map VariableToken t)). { intros. injection H4 as H4. apply H4. }
       apply H4. apply IHt; auto.
Qed.

Lemma overwrite_env : forall st0 d1 r1 b v c2 n, incl (variable_extraction c2) b -> length b = length v -> NoDup b ->
eval (st0, t_update_list d1 b v) (Application (extract_fun c2 (variable_extraction c2)) (Vars (map VariableToken (variable_extraction c2)))) n =
eval (st0, t_update_list r1 b v) (Application (extract_fun c2 (variable_extraction c2)) (Vars (map VariableToken (variable_extraction c2)))) n.
Proof.
  intros. revert d1 r1 b v n H H0 H1.
  induction c2.
  - intros. simpl in H. simpl.
    destruct n.
    -- simpl. auto.
    -- simpl. 
       destruct (eval (pair st0 (t_update_list d1 b v)) (Lambda nil (Vars nil)) n) eqn : E1; try discriminate.
       --- destruct n; try discriminate. simpl in E1. injection E1 as E1.
           rewrite <- E1. simpl. auto.
       --- destruct n; try discriminate. simpl. auto.
  - intros. erewrite <-  ! incl_equals in *. simpl. simpl in H. destruct n; auto. simpl. erewrite overwrite_env_vars; auto.
    -- instantiate (1 := r1). Admitted.



Lemma included_variables : forall x a X, incl (variable_extraction <{ x := a }>) X -> incl (x :: get_vars a) X.
Proof.
  intros. erewrite <- incl_equals in H. simpl in H. apply H.
Qed.

Lemma extract_fun_obtain_closure : forall c2 r1 r2 d1 c1 a b X v n, eval (token_update_list r1 (map VariableToken X) v)
    (extract_fun c2 X) n = Some [Closure a b c1 d1] -> exists d2, 
    eval (token_update_list r2 (map VariableToken X) v)
    (extract_fun c2 X) n = Some [Closure a b c1 d2].
Proof.
  intros c2.
  induction c2.
  - intros. simpl in *. destruct n; try discriminate. simpl in *. injection H as H. subst.
    exists (token_update_list r2 (map VariableToken X) v). auto.
  - intros. simpl in *. destruct n; try discriminate. simpl in *. injection H as H. subst.
    exists ((token_update_list r2 (map VariableToken X) v)). auto.
  - intros. simpl in *. destruct n; try discriminate. simpl in *. inversion H; subst.
    exists ((token_update_list r2 (map VariableToken X) v)); auto.
  - intros. Admitted.

Lemma closed_env : forall c r1 X a b c1 d1 n, (incl (variable_extraction c) X) ->
NoDup X -> eval r1 (extract_fun c X) n = Some [Closure a b c1 d1] ->
forall r2, exists d2, eval r2 (extract_fun c X) n =
Some [Closure a b c1 d2] /\ forall v, Datatypes.length b = Datatypes.length v ->
match a with 
| Some f => eval (token_update_list d1 (f::b) ((Closure a b c1 d1)::v)) c1 n = eval (token_update_list d2 (f::b) ((Closure a b c1 d2)::v)) c1 n
| None => eval (token_update_list d1 b v) c1 n = eval (token_update_list d2 b v) c1 n
end.
Proof.
  intros c.
  induction c; simpl in *; intros.
  - destruct n; try discriminate. simpl in H1. inversion H1; subst. simpl.
    eauto. exists r2. split; auto. intros. erewrite token_update_vars. erewrite map_over_tokens_vars.
    erewrite token_update_vars. erewrite map_over_tokens_vars. rewrite 2 step_gen; auto.
    erewrite map_length in H2; auto. erewrite map_length in H2; auto.
  - destruct n; try discriminate. simpl in H1. inversion H1; subst.
    exists r2. split; auto. intros. erewrite token_update_vars; auto. erewrite token_update_vars; auto. 
    eapply needed_for_closed_env; auto.
    erewrite map_length in H2. 
    -- eapply included_variables. auto.
    -- erewrite map_length in H2. apply H2.
  - destruct n; try discriminate. simpl in H1. inversion H1; subst. simpl.
    exists r2. split; auto. intros.
   Admitted.

Lemma length_make_conjunctions : forall X v st, make_conjunction X v st -> length X = length v.
Proof.
  intros X.
  induction X as [| x xs]; simpl; intros.
  - destruct v; auto. destruct H.
  - destruct v; auto. { destruct H. } simpl. apply f_equal. destruct H. eapply IHxs; eauto.
Qed.

Lemma less_implies_false : forall X v, (length X < length v) -> (make_conjunction X v ->> (fun st => False)).
Proof.
  intros X v. revert X.
  induction v as [| h t].
  - intros. unfold "->>". intros. simpl in H. lia.
  - intros.
    destruct X as [| x xs].
    -- simpl. auto.
    -- unfold "->>". intros. simpl in H. unfold "->>" in IHt. specialize IHt with (X:=xs). eapply IHt.
       --- Search "<". apply lt_S_n in H. auto.
       --- simpl in H0. destruct H0. apply m.
Qed.

Lemma greater_implies_false : forall X v, (length X > length v) -> (make_conjunction X v ->> (fun st => False)).
Proof.
  intros X.
  induction X as [| x xs].
  - intros. unfold "->>". intros. simpl in H. lia.
  - intros.
    destruct v as [| h t].
    -- simpl. auto.
    -- unfold "->>". intros. simpl in H. unfold "->>" in IHxs. specialize IHxs with (v:=t). eapply IHxs.
       --- Search "<". apply gt_S_n in H. auto.
       --- simpl in H0. destruct H0. apply m.
Qed.

(* what's up with this? *)
Lemma lt_redudant : forall n n0, negb (n <=? n0)%nat = (n0 <? n)%nat.
Proof.
  intros n.
  induction n; intros.
  - simpl.
    destruct n0; auto.
  - simpl.
    destruct n0; auto.
    rewrite IHn.
    Admitted.

Lemma simpl_conjunction : forall h t v vs st,
make_conjunction (h :: t) (v :: vs) st = ((st h = v) /\ make_conjunction t vs st).
Proof.
  intros h t.
  induction t as [| th tt].
  - intros. simpl. auto.
  - intros.
    destruct vs as [| vsh vst].
    -- simpl. auto.
    -- simpl. auto.
Qed.

Lemma conjunction_implies_st : forall X v st,
length X = length v -> NoDup X -> make_conjunction X v st -> map st X = v.
Proof.
  intros X.
  induction X as [| h t].
  - intros. simpl. Search length. simpl in H. symmetry in H. eapply length_zero_iff_nil in H. symmetry. apply H.
  - intros. simpl.
    destruct v as [| v vs].
    -- simpl in H. discriminate.
    -- simpl in H. injection H as H.
       erewrite simpl_conjunction in H1. destruct H1. subst. apply f_equal.
       eapply IHt; eauto. eapply NoDup_cons_iff in H0. destruct H0. apply H1.
Qed.

Lemma eval_bool : forall X v b x st bool (env : (total_map value * total_map value)) 
(Hsetvariables : map (snd env) X = (map Number v)),
incl (get_bvars b) X ->
length X = length v ->
make_conjunction X v st ->
eval env (bimp_to_functional b) x = Some [Boolean bool] ->
NoDup X ->
beval st b = bool.
Proof.
  intros X v b.
  induction b.
  - intros. simpl. simpl in H2. destruct x; try discriminate. simpl in H2. injection H2 as H2. auto.
  - intros. simpl. simpl in H2. destruct x; try discriminate. simpl in H2. injection H2 as H2. auto.
  - intros. simpl in H. apply incl_app_inv in H. destruct H.
    destruct x; try discriminate. simpl in H2.
    destruct (eval env (aimp_to_functional a1) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval env (aimp_to_functional a2) x) eqn : E2; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate. injection H2 as H2. simpl.
    destruct env.
    eapply environment_to_state in E1.
    3 : apply conjunction_implies_st; eauto.
    all : auto. assert (exists x, eval (t, compose Number st) (aimp_to_functional a1) x =
     Some [Number n]) by eauto.
    apply aeval_to_eval in H5. injection H5 as H5. rewrite H5.
    eapply environment_to_state in E2.
    3 : apply conjunction_implies_st; eauto.
    all : auto. assert (exists x, eval (t, compose Number st) (aimp_to_functional a2) x =
     Some [Number n0]) by eauto.
    apply aeval_to_eval in H6.
    injection H6 as H6. rewrite H6. auto.
  - (* intros. simpl in H. Search incl. apply incl_app_inv in H. destruct H.
    destruct x; try discriminate. simpl in H2.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a1) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a2) x) eqn : E2; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate. injection H2 as H2. simpl.
    eapply environment_to_state in E1.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E1.
    pose aeval_to_eval. specialize e with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a1) (v:=Number n).
    pose needed_for_one_gen. simpl.
    specialize e0 with (a:=a1) (X:=X) (v:=v) (st:=st). rewrite <- e0; auto.
    assert (exists n0 : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a1) n0 = Some [Number n]). { exists x. auto. }
    specialize (e H5). injection e as e. rewrite e.
    eapply environment_to_state in E2.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E2.
    pose aeval_to_eval.
    specialize e1 with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a2) (v:=Number n0).
    pose needed_for_one_gen.
    specialize e2 with (a:=a2) (X:=X) (v:=v) (st:=st). 
    rewrite <- e2; auto.
    rewrite e2; auto.
    assert (exists n : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a2) n = Some [Number n0]). { exists x. auto. }
    specialize (e1 H6). injection e1 as e1. rewrite e1 in e2. erewrite <- e2; auto.
  - intros. simpl in H. Search incl. apply incl_app_inv in H. destruct H.
    destruct x; try discriminate. simpl in H2.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a1) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a2) x) eqn : E2; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate. injection H2 as H2. simpl.
    eapply environment_to_state in E1.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E1.
    pose aeval_to_eval. specialize e with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a1) (v:=Number n).
    pose needed_for_one_gen. simpl.
    specialize e0 with (a:=a1) (X:=X) (v:=v) (st:=st). rewrite <- e0; auto.
    assert (exists n0 : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a1) n0 = Some [Number n]). { exists x. auto. }
    specialize (e H5). injection e as e. rewrite e.
    eapply environment_to_state in E2.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E2.
    pose aeval_to_eval.
    specialize e1 with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a2) (v:=Number n0).
    pose needed_for_one_gen.
    specialize e2 with (a:=a2) (X:=X) (v:=v) (st:=st). 
    rewrite <- e2; auto.
    rewrite e2; auto.
    assert (exists n : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a2) n = Some [Number n0]). { exists x. auto. }
    specialize (e1 H6). injection e1 as e1. rewrite e1 in e2. erewrite <- e2; auto.
  - intros. simpl in H. Search incl. apply incl_app_inv in H. destruct H.
    destruct x; try discriminate. simpl in H2.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a1) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval (set_variables X (map Number v)) (aimp_to_functional a2) x) eqn : E2; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate. injection H2 as H2. simpl.
    eapply environment_to_state in E1.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E1.
    pose aeval_to_eval. specialize e with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a1) (v:=Number n).
    pose needed_for_one_gen. simpl.
    specialize e0 with (a:=a1) (X:=X) (v:=v) (st:=st). rewrite <- e0; auto.
    assert (exists n0 : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a1) n0 = Some [Number n]). { exists x. auto. }
    specialize (e H5). injection e as e. rewrite e.
    eapply environment_to_state in E2.
    2 : apply H0. 2 : auto. instantiate (1 := empty_st) in E2.
    pose aeval_to_eval.
    specialize e1 with (st0:=fst empty_environment) (st:=(t_update_list empty_st X v)) (a:=a2) (v:=Number n0).
    pose needed_for_one_gen.
    specialize e2 with (a:=a2) (X:=X) (v:=v) (st:=st). 
    rewrite <- e2; auto.
    rewrite e2; auto.
    assert (exists n : nat,
       eval (fst empty_environment, compose Number (t_update_list empty_st X v)) 
         (aimp_to_functional a2) n = Some [Number n0]). { exists x. auto. }
    specialize (e1 H6). injection e1 as e1. rewrite e1 in e2. erewrite <- e2; auto.
    rewrite <- H2. Search Nat.leb Nat.ltb. symmetry. apply Nat.ltb_antisym.
  - intros. simpl. destruct x; try discriminate. simpl in H2.
    destruct (eval (set_variables X (map Number v)) (bimp_to_functional b) x) eqn : E; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct b0; try discriminate.
    -- destruct l; try discriminate. inversion H2; subst.
       Search negb. eapply negb_false_iff. eapply IHb; auto.
       apply E.
    -- destruct l; try discriminate. inversion H2; subst.
       eapply negb_true_iff. eapply IHb; auto. apply E.
  - intros. simpl in H. Search incl. apply incl_app_inv in H. destruct H.
    destruct x; try discriminate. simpl in H2.
    destruct (eval (set_variables X (map Number v)) (bimp_to_functional b1) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct b; try discriminate.
    destruct l; try discriminate.
    -- destruct (eval (set_variables X (map Number v)) (bimp_to_functional b2) x) eqn : E2; try discriminate.
       destruct l; try discriminate.
       destruct v0; try discriminate.
       destruct b; try discriminate.
       --- destruct l; try discriminate. inversion H2; subst.
           simpl. erewrite IHb1; auto. 2 : apply E1. erewrite IHb2; auto. 2 : apply E2.
           auto.
       --- destruct l; try discriminate. inversion H2; subst.
           simpl. erewrite IHb1; auto. 2 : apply E1. erewrite IHb2; auto. 2 : apply E2.
           auto.
    -- destruct (eval (set_variables X (map Number v)) (bimp_to_functional b2) x) eqn : E2; try discriminate.
       --- destruct l; try discriminate. destruct l0; try discriminate. destruct v0; try discriminate.
           destruct b; try discriminate.
           ---- destruct l0; try discriminate. inversion H2; subst. simpl. erewrite IHb1; auto. 2 : apply E1.
                erewrite IHb2; auto. apply E2; auto.
           ---- destruct l0; try discriminate. inversion H2; subst. simpl. erewrite IHb1; auto. 2 : apply E1.
                erewrite IHb2; auto. apply E2; auto.
       --- destruct l; try discriminate.
Qed. *) Admitted.

(*
Lemma extract_fun_same_lengths : forall c1 X x4 v n (env : (total_map value * total_map value))
       (Hlength : length X = length v) (HDup : NoDup X)
       (Hsetvariables : map (snd env) X = (map Number v)),
       eval (env) (Application ( extract_fun c1 X ) ( Vars (map VariableToken X) )) n =
       Some (map Number x4) -> length X = length x4.
Proof.
  intros c. intros. destruct n; try discriminate. simpl in H.
  (*
  destruct (eval (set_variables X (map Number v)) (extract_fun c X) n) eqn : E; try discriminate.
  destruct l; try discriminate.
  destruct v0; try discriminate.
  destruct l; try discriminate.
  destruct n; try discriminate. unfold eval at 1 in H. revert X x4 v n name args body env E H HDup Hlength.
  induction c; intros.
  - simpl in E. inversion E. subst. simpl in H. injection H as H.
    Search map. erewrite token_update_vars in H. erewrite map_over_tokens_vars in H. erewrite needed_for_reduce_again in H; auto.
    -- Search map. unfold set_variables in H. erewrite map_over_tokens_vars in H.  erewrite step in H; auto. Search length. rewrite Hlength.
       Search map. erewrite length_preserved; auto. erewrite length_preserved; auto.
       rewrite H. auto.
    -- erewrite needed_for_reduce_again in H; auto.
       --- unfold set_variables. erewrite map_over_tokens_vars. erewrite step; auto. unfold set_variables in H.
           erewrite map_over_tokens_vars in H.
           erewrite step in H; auto. erewrite <- length_preserved; auto.
       --- unfold set_variables. erewrite map_over_tokens_vars. erewrite step; auto. unfold set_variables in H.
           erewrite map_over_tokens_vars in H.
           erewrite step in H; auto. erewrite <- length_preserved; auto.
  - simpl in E.  inversion E; subst. simpl in H. 
    destruct (eval
        (token_update_list (set_variables X (map Number v))
           (map VariableToken X)
           (map_over_tokens (set_variables X (map Number v))
              (map VariableToken X))) (aimp_to_functional a) n) eqn : E1; try discriminate.
    destruct l; try discriminate.
    -- destruct n; try discriminate. simpl in H. injection H as H. erewrite token_update_vars in H.
       erewrite map_over_tokens_vars in H.
       erewrite needed_for_reduce_again in H; auto.
       --- unfold set_variables in H. erewrite map_over_tokens_vars in H.
           erewrite step in H; auto. erewrite length_preserved; auto.
           rewrite <- H. erewrite <- length_preserved. auto.
       --- unfold set_variables. erewrite map_over_tokens_vars. erewrite step; auto. erewrite <- length_preserved; auto.
    -- destruct n; try discriminate. simpl in H.
       destruct l; try discriminate.
       --- injection H as H. Search t_update_list.
           Search map. erewrite <- map_length. 
           erewrite map_over_tokens_vars in H. instantiate (1:=(x !-> v0;
       snd
         (token_update_list (set_variables X (map Number v))
            (map VariableToken X)
            (map_over_tokens (set_variables X (map Number v))
               (map VariableToken X))))). rewrite H. apply map_length; auto.
       --- injection H as H. erewrite <- map_length. erewrite map_over_tokens_vars in H. instantiate (1:=(x !-> v0;
       snd
         (token_update_list (set_variables X (map Number v))
            (map VariableToken X)
            (map_over_tokens (set_variables X (map Number v))
               (map VariableToken X))))). rewrite H. apply map_length.
  - simpl in E. inversion E; subst. simpl in H.
    destruct ( eval
        (token_update_list (set_variables X (map Number v))
           (map VariableToken X)
           (map_over_tokens (set_variables X (map Number v))
              (map VariableToken X))) (extract_fun c2 X) n) eqn : E2; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval
          (token_update_list (set_variables X (map Number v))
             (map VariableToken X)
             (map_over_tokens (set_variables X (map Number v))
                (map VariableToken X)))
          (Application (extract_fun c1 X) (Vars (map VariableToken X)))) eqn : E1; try discriminate.
    eapply IHc2; auto.
    -- unfold set_variables. unfold set_variables in E2. 
       erewrite token_update_vars in E2. simpl in E2.
       erewrite map_over_tokens_vars in E2. erewrite step_gen in E2; auto.
       --- Search t_update_list. erewrite two_updates in E2; auto. eapply plus_one_fuel in E2; auto.
           apply E2.
       --- erewrite map_length. auto.
    --*)
    Admitted.
*)

Lemma args_same_length : forall st0 X x4 c2 x name x1 x2 d2 env, 
eval (st0, t_update_list env X (map Number x4)) (extract_fun c2 X) x =
          Some [Closure name x1 x2 d2] -> x1 = map VariableToken X.
Proof.
  intros st0 X x4 c. revert X x4.
  induction c.
  - intros. simpl in H. destruct x; try discriminate. simpl in H. inversion H; subst. auto.
  - intros. simpl in H.
    destruct x; try discriminate.
    -- destruct x0; try discriminate. simpl in H. inversion H; subst; auto.
    -- destruct x0; try discriminate. simpl in H. inversion H; subst; auto.
  - intros. destruct x; try discriminate. simpl in H. inversion H; subst; auto. 
  - intros. destruct x; try discriminate. simpl in H. injection H as H. symmetry. apply H0.
  - intros. destruct x; try discriminate. simpl in H. inversion H; subst; auto.
Qed.

Arguments eval : simpl never.
(* this is fine. Qed runs forever *)
Lemma whilebody_induction : forall n z l env env' whilebody (Heqwhilebody : whilebody = (If
                    (Application
                       (Lambda (cons (VariableToken "y") (cons (VariableToken "x") nil))
                          (Greater (Vars (cons (VariableToken "x") nil)) (Num 0)))
                       (Vars (cons (VariableToken "y") (cons (VariableToken "x") nil))))
                    (Application (Vars (cons (FunctionToken "Whilefun") nil))
                       (Application
                          (Lambda (cons (VariableToken "y") (cons (VariableToken "x") nil))
                             (Application
                                (Lambda
                                   (cons (VariableToken "y") (cons (VariableToken "x") nil))
                                   (Let (VariableToken "x")
                                      (Minus (Vars (cons (VariableToken "x") nil)) (Num 1))
                                      (Vars
                                         (cons (VariableToken "y")
                                            (cons (VariableToken "x") nil)))))
                                (Application
                                   (Lambda
                                      (cons (VariableToken "y") (cons (VariableToken "x") nil))
                                      (Let (VariableToken "y")
                                         (Mult (Vars (cons (VariableToken "x") nil))
                                            (Vars (cons (VariableToken "y") nil)))
                                         (Vars
                                            (cons (VariableToken "y")
                                               (cons (VariableToken "x") nil)))))
                                   (Vars
                                      (cons (VariableToken "y") (cons (VariableToken "x") nil))))))
                          (Vars (cons (VariableToken "y") (cons (VariableToken "x") nil)))))
                    (Vars (cons (VariableToken "y") (cons (VariableToken "x") nil)))))
    (Heqinduction : (snd env) "x" = (Number n) /\ (snd env) "y" = (Number z) /\ (fst env) "Whilefun"
          = (Closure (Some (FunctionToken "Whilefun"))
                 [VariableToken "y"; VariableToken "x"]
                 whilebody (fst env', snd env'))),
    (exists m, eval env whilebody m =
    Some l) -> [Number (z * (factorial (n))); Number 0] = l.
Proof.
  assert ( ("y" <> "x") ) as Hneq. { eapply eqb_neq. auto. }
  intros. revert n l env env' z Heqinduction H.
  induction n; try discriminate.
  - intros. destruct H. destruct x; try discriminate. rewrite Heqwhilebody in H. rewrite eval_eq in H.
    destruct x; try discriminate. rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H.
    rewrite eval_eq in H. assert ((map VariableToken ["y";"x"]) = [VariableToken "y"; VariableToken "x"]).
    { auto. } rewrite <- H0 in H. simpl in H. rewrite eval_eq in H. destruct x; try discriminate.
    rewrite eval_eq in H. assert ([VariableToken "x"] = map VariableToken ["x"]). { auto. } rewrite H1 in H.
    erewrite map_over_tokens_vars in H. simpl in H. erewrite ! t_update_same in H; auto. destruct Heqinduction.
    destruct H3.
    setoid_rewrite H2 in H. assert ((0 <? 0)%nat = false). { auto. } rewrite H5 in H.
    rewrite eval_eq in H. rewrite <- H0 in H. injection H as H. setoid_rewrite H2 in H. setoid_rewrite H3 in H.
    simpl. assert ((z*1) = z). { lia. } rewrite H6. apply H.
  - intros. destruct H. destruct Heqinduction. destruct H1. rewrite Heqwhilebody in H. destruct x; try discriminate.
    rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H. destruct x; try discriminate.
    rewrite eval_eq in H. rewrite eval_eq in H. assert ((map VariableToken ["y";"x"]) = [VariableToken "y"; VariableToken "x"]).
    { auto. } rewrite <- H3 in H. erewrite token_update_vars in H. simpl in H. setoid_rewrite H0 in H; setoid_rewrite H1 in H.
    rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H. assert ([VariableToken "x"] = map VariableToken ["x"]). 
    { auto. } rewrite H4 in H. erewrite map_over_tokens_vars in H. simpl in H. rewrite eval_eq in H. rewrite eval_eq in H.
    assert ([FunctionToken "Whilefun"] = map FunctionToken ["Whilefun"]). { auto. } rewrite H5 in H.
    pose decompose_prod as Hdecompose. specialize Hdecompose with (env:=env). rewrite Hdecompose in H.
    unfold map_over_tokens at 1 in H. rewrite <- H5 in H. simpl in H. setoid_rewrite H2 in H. rewrite eval_eq in H.
    rewrite eval_eq in H. rewrite eval_eq in H. rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H.
    rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H. rewrite eval_eq in H. rewrite <- H3 in H.
    erewrite token_update_vars in H. simpl in H. erewrite ! t_update_eq in H. erewrite t_update_neq in H; auto.
    erewrite t_update_eq in H. erewrite ! t_update_same in H. rewrite eval_eq in H. destruct x; try discriminate.
    rewrite eval_eq in H. destruct x; try discriminate. rewrite eval_eq in H. rewrite H4 in H. erewrite map_over_tokens_vars in H.
    simpl in H. setoid_rewrite H0 in H. setoid_rewrite H1 in H. simpl in H. erewrite ! t_update_eq in H. erewrite t_update_neq in H; auto.
    rewrite eval_eq in H. rewrite eval_eq in H. setoid_rewrite H0 in H. rewrite eval_eq in H. rewrite H4 in H.
    erewrite map_over_tokens_vars in H. simpl in H. erewrite ! t_update_eq in H. erewrite t_update_neq in H; auto.
    erewrite t_update_eq in H. assert (n-0 = n). { destruct n. - auto. -lia. } rewrite H6 in H.
    assert ((z * (S n)) * factorial (n) = z * factorial (S n)). { destruct n. - simpl. lia. - simpl. lia. }
    rewrite <- H7. eapply IHn.
    -- instantiate (3:=("Whilefun"
       !-> Closure
             (Some (FunctionToken "Whilefun"))
             [VariableToken "y"; VariableToken "x"]
             whilebody (fst env', snd env'); 
       fst env',
      "y" !-> Number (z + n * z);
      "x" !-> Number n; snd env')). auto. split.
       --- simpl. erewrite t_update_neq; auto.
       --- split.
           ---- simpl. erewrite t_update_eq. apply f_equal. lia.
           ---- simpl. instantiate (1:=env'). simpl. erewrite t_update_eq. auto.
    -- exists ((S (S (S (S (S (S x))))))). apply H.
Admitted.

Theorem equals_factorial : forall n l env (Henv : (snd env) "x" = (Number n)),
(exists m, eval env (Application function_example (Vars [VariableToken "y"; VariableToken "x"])) m = Some l) ->
l = [Number (factorial n); Number 0].
Proof.
  assert ("y" =? "x" = false) as H0. { auto. } assert ( ("y" <> "x") ) as Primitive. { eapply eqb_neq in H0. apply H0. }
  intros. destruct H. destruct x; try discriminate. rewrite eval_eq in H. unfold function_example in H.
    unfold example in H. simpl extract_fun in H. unfold Whilefun in H. destruct x; try discriminate. rewrite eval_eq in H.
    simpl in H. rewrite eval_eq in H. destruct x; try discriminate. simpl in H. rewrite eval_eq in H.
    destruct x; try discriminate. simpl in H. rewrite eval_eq in H. destruct x; try discriminate. simpl in H.
    symmetry. replace (factorial n) with (1 * (factorial (n))). eapply whilebody_induction; eauto.
    simpl. clear. erewrite ! t_update_same.
    erewrite ! t_update_eq. erewrite t_update_neq; auto. lia.
Qed.

Arguments eval _ _ !_ .

Lemma pre_redundant_eval_env : forall ls X v (env : (total_map value * total_map value)) 
(Hsetvariables : map (snd env) X = (map Number v)),
map_over_tokens (fst env, t_update_list (snd env) X (map Number v)) ls =
map_over_tokens (fst env, snd env) ls.
Proof.
  induction ls.
  - intros. simpl. auto.
  - intros. simpl.
    destruct a.
    -- apply f_equal. eapply IHls. apply Hsetvariables.
    -- Search t_update_list. rewrite <- Hsetvariables. erewrite equivalent_env_update_redux. auto.
Qed.

Lemma redundant_eval_env : forall X v f x l (env : (total_map value * total_map value)) 
(Hsetvariables : map (snd env) X = (map Number v)),
eval (fst env, t_update_list (snd env) X (map Number v)) f x = Some l ->
eval (fst env, snd env) f x = Some l.
Proof.
  intros X v f. revert X v.
  induction f.
  - intros. destruct x; try discriminate. simpl in H. simpl. auto.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in *. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct l0; try discriminate. 
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate. 
    destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate. simpl.
    erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in *. destruct (eval (fst env, t_update_list (snd env) X (map Number v))
        f x) eqn : E; try discriminate. destruct l0; try discriminate. destruct v0; try discriminate.
    destruct b; try discriminate.
    -- destruct l0; try discriminate. erewrite IHf; eauto. simpl. apply H.
    -- destruct l0; try discriminate. erewrite IHf; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in H.
    destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f1
        x) eqn : E1; try discriminate.
    destruct l0; try discriminate. destruct v0; try discriminate. 
    destruct b; try discriminate.
    -- destruct l0; try discriminate.
       destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate.
       destruct l0; try discriminate. destruct v0; try discriminate.
       --- destruct b; try discriminate.
           ---- destruct l0; try discriminate. simpl.
                erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
           ---- destruct l0; try discriminate. simpl.
                erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
    -- destruct l0; try discriminate.
       destruct ( eval (fst env, t_update_list (snd env) X (map Number v)) f2
        x) eqn : E2; try discriminate.
       destruct l0; try discriminate. destruct v0; try discriminate.
       --- destruct b; try discriminate.
           ---- destruct l0; try discriminate. simpl.
                erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
           ---- destruct l0; try discriminate. simpl.
                erewrite IHf1; eauto. simpl. erewrite IHf2; eauto. simpl. apply H.
  - intros. destruct x; try discriminate. simpl in *. Search t_update_list. apply f_equal.
    injection H as H. rewrite <- H. symmetry. apply pre_redundant_eval_env. apply Hsetvariables.
  - intros. destruct x; try discriminate. simpl in *.
    destruct (eval (fst env, t_update_list (snd env) X (map Number v)) f1 x) eqn : E1; try discriminate.
    destruct l0; try discriminate.
    -- erewrite IHf1; eauto. simpl. eapply IHf2; eauto.
    -- erewrite IHf1; eauto. simpl. Search t_update_list. rewrite <- Hsetvariables in H.
       erewrite equivalent_env_update_redux in H. apply H.
  - intros. destruct x; try discriminate. simpl in *.
    destruct (eval (fst env, t_update_list (snd env) X (map Number v)) f1 x) eqn : E; try discriminate.
    destruct l0 eqn : B; try discriminate.
    destruct v0; try discriminate.
    destruct b eqn : B1; try discriminate.
    -- destruct l1; try discriminate. erewrite IHf1; eauto. simpl. eapply IHf2; eauto.
    -- destruct l1; try discriminate. erewrite IHf1; eauto. simpl. eapply IHf3; eauto.
  - intros. destruct x; try discriminate. simpl in *. rewrite <- Hsetvariables in H. 
    erewrite equivalent_env_update_redux in H. apply H.
  - intros. destruct x; try discriminate. simpl in *.
    destruct (eval (fst env, t_update_list (snd env) X (map Number v)) f1 x) eqn : E1; try discriminate.
    destruct l0; try discriminate.
    destruct v0; try discriminate.
    destruct l0; try discriminate. erewrite IHf1; eauto. simpl.
    destruct (eval (fst env, t_update_list (snd env) X (map Number v)) f2 x) eqn : E2; try discriminate.
    erewrite IHf2; eauto.
  - intros. destruct x; try discriminate. simpl in *. erewrite <- Hsetvariables in H.
    erewrite equivalent_env_update_redux in H. apply H.
Qed.

Lemma map_over_tokens_function : forall env1 env2 X, map_over_tokens (env1, env2) (map FunctionToken X) = map env1 X.
Proof.
  intros. revert env1 env2.
  induction X.
  - intros. simpl. auto.
  - intros. simpl. apply f_equal. apply IHX.
Qed.

Lemma token_update_list_function_vars : forall (env : (total_map value * total_map value)) X name v0 v,
token_update_list env (FunctionToken name :: map VariableToken X) (v0 :: v) =
(t_update (fst env) name v0, t_update_list (snd env) X v).
Proof.
  intros. revert env name v0 v.
  induction X as [| x xs].
  - intros. simpl.
    destruct v as [| v vs].
    -- auto.
    -- auto.
  - intros. simpl.
    destruct v as [| v vs].
    -- auto.
    -- simpl. erewrite token_update_vars. simpl. auto.
Qed.

Lemma map_over_list : forall x y (m : total_map value), map (x !-> y; m) [x] = [y].
Proof.
  intros. simpl. erewrite t_update_eq. auto.
Qed.

Theorem main : forall v v' X c env (Hsetvariables : map (snd env) X = (map Number v)) ,
(NoDup X) ->
(exists n, (eval env (Application (extract_fun c X) (Vars (map VariableToken X))) n) = Some (map Number v')) ->
(incl (variable_extraction c) X) ->
({{make_conjunction ((X)) v}} c {{make_conjunction ((X)) v'}}).
Proof.
  intros v v' X c. revert v v' X.
  induction c.
  - intros v v' X env H1 H2 H3. simpl in H3. destruct H3. destruct x; try discriminate. simpl in H. destruct x; try discriminate. simpl in H. injection H as H.
    pose destruct_length as H3. specialize H3 with (n:=length X) (m:=length v).
    destruct H3.
    -- pose less_than as H3. specialize H3 with (X:=X) (v:=v). specialize (H3 H0). intros.
       apply hoare_consequence_pre with (P':=fun _ : state => False).
       --- unfold hoare_triple. intros st st' H5 H6. destruct H6.
       --- apply H3.
    -- destruct H0.
       --- pose greater_than as H3. specialize H3 with (X:=X) (v:=v). specialize (H3 H0). intros.
           apply hoare_consequence_pre with (P':=fun _ : state => False).
           ---- unfold hoare_triple. intros st st' H5 H6. destruct H6.
           ---- apply H3.
       --- intros. pose step as H4. specialize H4 with (X:=X) (v:=v) (env:=env). specialize (H4 H0).
           specialize (H4 H2). erewrite token_update_vars in H. erewrite map_over_tokens_vars in H. replace (env) with ((fst env, snd env)) in H.
           2 : {symmetry. eapply decompose_prod. }
           erewrite map_over_tokens_vars in H. rewrite H1 in H. simpl in H.
           setoid_rewrite H in H4.
           ---- apply unfold_map_Number in H4. rewrite H4. apply hoare_skip.
  - intros v v' X env Hsetvariables H1 H2 H3. eapply hoare_consequence_pre. eapply hoare_asgn.
    unfold "->>". intros st. intros Hconj. simpl in H2. destruct H2. destruct x0; try discriminate. simpl in H. destruct x0; try discriminate. simpl in H.
    unfold set_variables in H.
    pose destruct_length as H2. specialize H2 with (n:=length X) (m:=length v).
    destruct H2.
    -- pose less_than as H2. specialize H2 with (X:=X) (v:=v). specialize (H2 H0).
       specialize (H2 _ Hconj). simpl in H2. destruct H2.
    -- destruct H0.
       --- pose greater_than as H2. specialize H2 with (X:=X) (v:=v). specialize (H2 H0).
           specialize (H2 _ Hconj). destruct H2.
       --- erewrite token_update_vars in H. replace env with (fst env, snd env) in H. 2: {symmetry. eapply decompose_prod. }
           erewrite map_over_tokens_vars in H. simpl in H. rewrite Hsetvariables in H.
           destruct  (eval (fst env, t_update_list (snd env) X (map Number v))
           (aimp_to_functional a) x0) eqn : H2 in H; try discriminate.
           destruct l as [| h t] eqn : H5; try discriminate.
           ---- exfalso. eapply blank. 3: eauto. all: eauto. Search map t_update_list. eapply needed_for_reduce_again; eauto.
                rewrite map_length. auto.
           ---- destruct t; try discriminate.
                ----- simpl in H3. pose incl_cons_inv. pose included_variables as IV.
                      eapply IV in H3.
                      specialize a0 with (A:=string) (a:=x) (l:=get_vars a) (m:=X).
                      specialize (a0 H3). destruct a0. eapply environment_to_state in H2; eauto.
                      2 : { eapply conjunction_implies_st in Hconj; eauto. rewrite Hconj.
                      eapply needed_for_reduce_again; eauto. erewrite map_length. auto. }
                      assert (exists x0, eval (fst env, compose Number st) (aimp_to_functional a) x0 =
                      Some [h]) by eauto.
                      apply aeval_to_eval in H7.
                      unfold assn_sub. eapply two; eauto. erewrite last_step; eauto. subst. eauto.
                      rewrite map_length. auto.
                ----- unfold assn_sub. eapply two; eauto.
                      (*assert (exists x0, eval (fst env, t_update_list (snd env) X (map Number v))
                      (aimp_to_functional a) x0 = Some (h :: v0 :: t)) by eauto.
                      eapply aimp_to_functional_one_value in H4; eauto.*)
                      pose aimp_to_functional_one_value. specialize e with (st0:=fst env) (X:=X) (v:=v) (a:=a) (l:=h :: v0 :: t)
                      (env:=snd env). specialize (e Hsetvariables H0). simpl in H3. pose incl_cons_inv.
                      specialize a0 with (A:=string) (a:=x) (l:=get_vars a) (m:=X).
                      pose included_variables as IV. eapply IV in H3. specialize (a0 H3).
                      destruct a0. specialize (e H6). assert (exists x0 : nat,
                      eval (fst env, t_update_list (snd env) X (map Number v))
                      (aimp_to_functional a) x0 = Some (h :: v0 :: t)). { exists x0. apply H2. } 
                      Search eval t_update_list. rewrite <- Hsetvariables in H7.
                      destruct H7. eapply redundant_t_update_eval in H7; eauto.
                      assert (exists x0, eval (fst env, snd env) (aimp_to_functional a)
                      x0 = Some (h :: v0 :: t)) by eauto.
                      specialize (e H8). destruct e.
                      discriminate.
  - intros v v' X env Hsetvariables H1 H2 H3. simpl in H2. destruct H2; try discriminate. destruct x in H; try discriminate. simpl in H.
    destruct x in H; try discriminate. simpl in H.
    destruct (eval
        (token_update_list env (map VariableToken X)
           (map_over_tokens env (map VariableToken X)))
        (extract_fun c2 X) x) eqn : E; try discriminate. pose extract_limits as E1.
    erewrite token_update_vars in E.
    specialize E1 with (X:=X) (c:=c2) (env:=(t_update_list (snd env) X
        (map_over_tokens env (map VariableToken X)))) (x:=x) (l:=l) (st0:=fst env).
    specialize (E1 E).
    destruct E1. destruct H0. destruct H0. destruct H0. rewrite H0 in H.
    destruct (eval
          (token_update_list env
             (map VariableToken X)
             (map_over_tokens env
                (map VariableToken X)))
          (Application (extract_fun c1 X)
             (Vars (map VariableToken X))) x) eqn : E2 in H; try discriminate.
    pose destruct_length as E3. specialize E3 with (n:=length X) (m:=length v).
    destruct E3.
    -- apply less_than in H2. unfold hoare_triple. unfold "->>" in H2.
       intros st st'. intros St. intros Hconj. specialize H2 with (st:=st).
       specialize (H2 Hconj).
       destruct H2.
    -- destruct H2.
       --- apply greater_than in H2.  unfold hoare_triple. unfold "->>" in H2.
           intros st st'. intros St. intros Hconj. specialize H2 with (st:=st).
           specialize (H2 Hconj). destruct H2.
       --- pose must_obtain_numbers. specialize e with (env:=env) (c:=c1) (X:=X) (n:=x) (l:=l0) (v:=v).
           specialize (e Hsetvariables).
           specialize (e H1). specialize (e H2). replace env with (fst env, snd env) in E2. 2 :  {symmetry. eapply decompose_prod. }
           erewrite map_over_tokens_vars in E2. rewrite Hsetvariables in E2. erewrite <- incl_equals in H3.
           erewrite token_update_vars in E2. erewrite need_for_fst in E2.
           erewrite need_for_snd in E2. eapply redundant_eval_env in E2; eauto.
           replace env with (fst env, snd env) in e. 2 : {erewrite decompose_prod. auto. }
           specialize (e E2). simpl in H3. apply incl_app_inv in H3.
           destruct H3. specialize (e H3). destruct e. rewrite H5 in E2.
           specialize IHc1 with (env:=env) (v:=v) (v':=x4) (X:=X). specialize (IHc1 Hsetvariables).
           specialize (IHc1 H1). assert ((exists n : nat,
           eval (fst env, snd env) (Application ( extract_fun c1 X ) ( Vars (map VariableToken X) )) n =
           Some (map Number x4))). { exists x. apply E2. } replace env with (fst env, snd env) in IHc1.
           2 : {erewrite decompose_prod. auto. }
           specialize (IHc1 H6).
           assert (length X = length x4). { destruct H6. destruct env. eapply extract_fun_same_lengths; eauto. } erewrite incl_equals in H3, H4. eapply hoare_seq, IHc1; eauto. 
           eapply (IHc2 _ _ _ (token_update_list env (map VariableToken X) (map Number x4))); eauto.
           ---- subst. simpl. Search token_update_list. erewrite token_update_vars. simpl. Search t_update_list. erewrite needed_for_reduce_again; auto.
                rewrite map_length. auto.
           ---- exists (S x). simpl. subst. destruct env in E.
                erewrite map_over_tokens_vars in E. simpl in E.
                pose reduce_set_variables as E'. unfold set_variables in E'. 
                specialize E' with (X:=X) (v:=v). erewrite need_for_snd in E'. specialize (E' H1).
                specialize (E' H2).
                destruct (eval (token_update_list env (map VariableToken X)
                (map Number x4)) (extract_fun c2 X) x) eqn : E1; try discriminate.
                + subst. fold get_variables in H4. eapply incl_equals in H4. eapply closed_env in E; auto.
                  destruct E as [d2 [eval_eq equals]]. rewrite eval_eq in E1. inversion E1; subst.
                  destruct x; try discriminate. unfold eval at 1.
                  destruct x0 eqn : Ename; try discriminate.
                  ++ erewrite ! token_update_vars. erewrite map_over_tokens_vars.
                     rewrite step; eauto. unfold token_update_list in equals.
                     unfold token_update_list. rewrite <- equals; auto.
                     erewrite map_length. rewrite <- H7. erewrite token_update_vars in eval_eq. eapply args_same_length in eval_eq.
                     rewrite eval_eq. auto. eapply map_length.
                  ++ erewrite token_update_vars. erewrite map_over_tokens_vars. rewrite step; auto. rewrite <- equals; auto.
                     erewrite map_length. rewrite <- H7. erewrite token_update_vars in eval_eq. eapply args_same_length in eval_eq.
                     rewrite eval_eq. eapply map_length.
                  ++ eapply incl_equals in H4. eapply closed_env in E; auto.
                + eapply closed_env in E; auto. destruct E. destruct H0. instantiate (1:=(token_update_list env (map VariableToken X)
                  (map Number x4))) in H0. rewrite H0 in E1. discriminate E1.
  - intros. destruct H0. destruct x; try discriminate.
    simpl in H0.
    destruct (eval env
           (Lambda (map VariableToken X)
              (If (bimp_to_functional b)
                 (Application (extract_fun c1 X)
                    (Vars (map VariableToken X)))
                 (Application (extract_fun c2 X)
                    (Vars (map VariableToken X))))) x) eqn : E1; try discriminate.
    destruct l; try discriminate.
    destruct v0; try discriminate.
    destruct l; try discriminate.
    destruct (eval env
         (Vars (map VariableToken X)) x) eqn : E2; try discriminate.
    destruct name.
    -- destruct x; try discriminate. (* simpl in E1.
       destruct (eval (set_variables X (map Number v)) (bimp_to_functional b) x) eqn : B; try discriminate.
       destruct l0; try discriminate.
       destruct v0; try discriminate.
       destruct b0; try discriminate.
       --- destruct l0; try discriminate. eapply hoare_if.
           ---- unfold hoare_triple. unfold hoare_triple in IHc1. intros. destruct H3.
                simpl in H1. Search incl. eapply incl_app_inv in H1. destruct H1.
                eapply incl_app_inv in H5. destruct H5.
                eapply IHc1. 1 : auto. 3 : apply H2. 3 : apply H3. 2 : apply H5.
                exists (S (S x)). remember (S x) as m. simpl.
                eapply plus_one_fuel in E1. subst. rewrite E1. rewrite E2. auto.
           ---- unfold hoare_triple. unfold hoare_triple in IHc2. intros. destruct H3. simpl in H4.
                Search "<>". eapply not_true_iff_false in H4. erewrite eval_bool in H4; auto.
                5 : apply B; auto. simpl in H1. Search incl. eapply incl_app_inv in H1.
                destruct H1. 4 : apply H3. 4: auto.
                ----- discriminate H4.
                ----- simpl in H1. eapply incl_app_inv in H1. destruct H1. auto.
                ----- eapply length_make_conjunctions; eauto.
       --- destruct l0; try discriminate. eapply hoare_if.
           ---- unfold hoare_triple. intros. unfold hoare_triple in IHc2. destruct H3.
                simpl in H4. erewrite eval_bool in H4. 5 : apply B; auto. 4 : auto. 4 : auto.
                ----- discriminate H4. 
                ----- simpl in H1. eapply incl_app_inv in H1. destruct H1. auto.
                ----- eapply length_make_conjunctions; eauto. 
           ---- unfold hoare_triple. intros. unfold hoare_triple in IHc2. destruct H3.
                simpl in H1. Search incl. eapply incl_app_inv in H1. destruct H1.
                eapply incl_app_inv in H5. destruct H5.
                eapply IHc2. 1 : auto. 2 : apply H6. 2 : apply H2. 2 : apply H3.
                exists (S (S x)). remember (S x) as m. simpl.
                eapply plus_one_fuel in E1. subst. rewrite E1. rewrite E2. auto. *)
    -- destruct x; try discriminate. simpl in E1. inversion E1; subst. simpl in H0.
       destruct (eval
         (token_update_list env0
            (map VariableToken X) l) (bimp_to_functional b) x) eqn : B; try discriminate.
       destruct l0; try discriminate.
       destruct v0; try discriminate.
       destruct b0; try discriminate.
       --- destruct l0; try discriminate. eapply hoare_if.
           ---- unfold hoare_triple. unfold hoare_triple in IHc1. intros. destruct H3. erewrite <- incl_equals in H1.
                simpl in H1. eapply incl_app_inv in H1. destruct H1.
                eapply incl_app_inv in H5. destruct H5.
                eapply IHc1; eauto. 2 : erewrite <- incl_equals. 2 : apply H5.
                exists (S (S x)). remember (S x) as m. simpl.
                destruct x; try discriminate. simpl in H0. destruct (eval
                (token_update_list env0
                (map VariableToken X) l) (extract_fun c1 X) x) eqn : E3; try discriminate.
                destruct l0; try discriminate. destruct v0; try discriminate. destruct l0; try discriminate.
                destruct (eval
                (token_update_list env0
                (map VariableToken X) l) (Vars (map VariableToken X))
                x) eqn : E4; try discriminate. rewrite E2. rewrite Heqm in E2. simpl in E2. injection E2 as E2. rewrite <- E2 in E3.
                unfold set_variables in E3. destruct env0 eqn : Hsplit in E3.
                erewrite map_over_tokens_vars in E3. erewrite token_update_vars in E3.
                simpl in E3.
                eapply plus_one_fuel in E3. eapply plus_one_fuel in E3.
                simpl in Hsetvariables. replace t0 with (snd env0) in E3; eauto.
                2 : { rewrite Hsplit. auto. } 
                replace t with (fst env0) in E3. 2: { rewrite Hsplit. auto. }
                setoid_rewrite Hsetvariables in E3. eapply redundant_eval_env in E3; eauto. rewrite Heqm. subst. Search fst.
                erewrite need_for_fst in E3. erewrite need_for_snd in E3.
                setoid_rewrite E3.
                destruct name.
                ----- eapply plus_one_fuel in H0. eapply plus_one_fuel in H0. destruct x; try discriminate.
                      simpl in E4. injection E4 as E4. rewrite <- E4 in H0. unfold set_variables in H0.
                      erewrite map_over_tokens_vars in H0. erewrite token_update_vars in H0. erewrite map_over_tokens_vars in H0.
                      erewrite need_for_snd in H0. unfold set_variables. erewrite map_over_tokens_vars. erewrite needed_for_reduce_again in H0.
                      3:auto. apply H0. Search length. erewrite map_length. auto.
                ----- destruct x; try discriminate. simpl in E4. injection E4 as E4. rewrite <- E4 in H0. eapply plus_one_fuel in H0.
                      eapply plus_one_fuel in H0. unfold set_variables. erewrite map_over_tokens_vars. unfold set_variables in H0.
                      erewrite map_over_tokens_vars in H0. erewrite token_update_vars in H0. erewrite need_for_fst in H0.
                      erewrite map_over_tokens_vars in H0. erewrite need_for_snd in H0. erewrite needed_for_reduce_again in H0. 3:auto.
                      apply H0. erewrite map_length. auto.
           ---- unfold hoare_triple. unfold hoare_triple in IHc2. intros. destruct H3. simpl in H4.
                eapply not_true_iff_false in H4.
                erewrite eval_bool in H4; eauto.
                3 : { erewrite <- map_length. rewrite Hsetvariables. eapply map_length. }
                2 : { simpl in H1. erewrite <- incl_equals in H1. simpl in H1. eapply incl_app_inv in H1. destruct H1. apply H1. }
                2 : { erewrite token_update_vars in B. simpl in E2. injection E2 as E2. 
                      destruct env0. erewrite map_over_tokens_vars in E2.
                      rewrite <- E2 in B. simpl in B. eapply redundant_t_update_eval; eauto. }
                discriminate.
       --- destruct l0; try discriminate. eapply hoare_if.
           ---- unfold hoare_triple. intros. unfold hoare_triple in IHc2. destruct H3. erewrite <- incl_equals in H1.
                simpl in H1. eapply incl_app_inv in H1. destruct H1.
                eapply incl_app_inv in H5. destruct H5. simpl in H4. erewrite eval_bool in H4; eauto.
                3:{ unfold set_variables in B. erewrite token_update_vars in B.
                    simpl in E2. injection E2 as E2. destruct env0. erewrite map_over_tokens_vars in E2. simpl in B.
                    rewrite <- E2 in B. eapply redundant_t_update_eval in B; eauto. }
                2:{ erewrite <- map_length. rewrite Hsetvariables. eapply map_length. }
                discriminate.
           ---- unfold hoare_triple. intros. unfold hoare_triple in IHc2. destruct H3. erewrite <- incl_equals in H1.
                simpl in H1. eapply incl_app_inv in H1. destruct H1.
                eapply incl_app_inv in H5. destruct H5.
                eapply IHc2; eauto. 2 : erewrite <- incl_equals. 2: apply H6.
                simpl in E2. injection E2 as E2. destruct env0. erewrite map_over_tokens_vars in E2.
                rewrite <- E2 in H0. erewrite token_update_vars in H0. simpl in H0. 
                eapply redundant_t_update_eval in H0; eauto.
  - intros. eapply hoare_consequence with (P':=fun st => exists v, make_conjunction X v st /\ exists env,
       map (snd env) X = map Number v /\ exists n : nat,
       eval (env)
         (Application ( extract_fun <{ while b do c end }> X ) ( Vars (map VariableToken X) )) n =
       Some (map Number v')). eapply hoare_while.
    -- simpl extract_fun. unfold Whilefun. unfold hoare_triple. intros.
       destruct H3 as ((v0 & (Hstate & (env0 & Hsetvariables' & (n & Whileworks)))) & Hb).
       destruct n; try discriminate. simpl in Whileworks.
       destruct (eval env0
                   (Rec (FunctionToken "Whilefun") (map VariableToken X)
                      (If
                         (Application (Lambda (map VariableToken X) (bimp_to_functional b))
                            (Vars (map VariableToken X)))
                         (Application (Vars (cons (FunctionToken "Whilefun") nil))
                            (Application (extract_fun c X) (Vars (map VariableToken X))))
                         (Vars (map VariableToken X)))) n) eqn : E; try discriminate.
       destruct l; try discriminate.
       destruct v1; try discriminate.
       destruct l; try discriminate.
       destruct (eval env0 (Vars (map VariableToken X)) n) eqn : E1; try discriminate.
       destruct n; try discriminate. simpl in E. inversion E. subst.
       simpl in Whileworks.
       erewrite token_update_vars in Whileworks. erewrite ! need_for_fst in Whileworks.
       erewrite ! need_for_snd in Whileworks. simpl in E1. destruct env1 eqn : Hfstsnd.
       erewrite map_over_tokens_vars in E1. injection E1 as E1. simpl in Whileworks.
       destruct (eval) eqn : Hb'; try discriminate.
       destruct l0 eqn : El0; try discriminate. destruct v1 eqn : Ev1; try discriminate.
       destruct l1; try (destruct b0; discriminate). assert (b0 = true).
       { unfold bassn in Hb. rewrite <- Hb. symmetry. 
         destruct n in Hb'; try discriminate. simpl in Hb'.
         destruct n in Hb'; try discriminate. rewrite eval_eq in Hb'. remember (S n) as m in Hb'.
         rewrite Heqm in Hb' at 1. simpl in Hb'.
         erewrite token_update_vars in Hb'. erewrite need_for_fst in Hb'.
         erewrite need_for_snd in Hb'. erewrite map_over_tokens_vars in Hb'. 
         erewrite needed_for_reduce_again in Hb'; eauto. 2 : { rewrite <- E1. symmetry. eapply map_length. }
         eapply eval_bool; auto.
         5 : apply Hb'. instantiate (2:=X). instantiate (1:=v0).
         - simpl. erewrite two_updates. simpl in Hsetvariables'. rewrite Hsetvariables' in E1.
           rewrite E1. eapply needed_for_reduce_again; eauto. rewrite <- E1. rewrite <- Hsetvariables'.
           symmetry. eapply map_length.
         - Search variable_extraction. eapply incl_equals in H1. simpl in H1.
           Search incl. eapply incl_app_inv in H1. destruct H1. apply H1.
         - symmetry. erewrite <- map_length. instantiate (1:=Number). symmetry.
           erewrite <- map_length. simpl in Hsetvariables'. instantiate (1:=t0).
           rewrite <- Hsetvariables'. auto.
         - apply Hstate.
         - apply H. } subst.
       destruct n; try discriminate. simpl in Whileworks.
       destruct n; try discriminate. rewrite eval_eq in Whileworks.
       replace [FunctionToken "Whilefun"] with (map FunctionToken ["Whilefun"]) in Whileworks; auto.
       erewrite map_over_tokens_function in Whileworks. 
       erewrite map_over_list in Whileworks.
       destruct (eval
                   (pair
                      (t_update t "Whilefun"
                         (Closure (Some (FunctionToken "Whilefun"))
                            (map VariableToken X)
                            (If
                               (Application
                                  (Lambda (map VariableToken X)
                                     (bimp_to_functional b))
                                  (Vars (map VariableToken X)))
                               (Application
                                  (Vars
                                     (map FunctionToken
                                        (cons "Whilefun" nil)))
                                  (Application 
                                     (extract_fun c X)
                                     (Vars (map VariableToken X))))
                               (Vars (map VariableToken X)))
                            (pair t t0)))
                      (t_update_list t0 X (map t0 X)))
                   (Application (extract_fun c X)
                      (Vars (map VariableToken X))) 
                   (S n)) eqn : Hb''; try discriminate.
       assert (exists v1, l = map Number v1).
       { eapply must_obtain_numbers; auto.
         - instantiate (1:=v0). instantiate (1:=X). instantiate (1:=(pair
               (t_update t "Whilefun"
                  (Closure (Some (FunctionToken "Whilefun"))
                     (map VariableToken X)
                     (If
                        (Application
                           (Lambda (map VariableToken X)
                              (bimp_to_functional b))
                           (Vars (map VariableToken X)))
                        (Application
                           (Vars
                              (map FunctionToken (cons "Whilefun" nil)))
                           (Application (extract_fun c X)
                              (Vars (map VariableToken X))))
                        (Vars (map VariableToken X))) 
                     (pair t t0))) (t_update_list t0 X (map t0 X)))). simpl.
          simpl in Hsetvariables'.
          rewrite Hsetvariables'. eapply needed_for_reduce_again; eauto.
          erewrite <- map_length. instantiate (1:=t0). rewrite Hsetvariables'. auto.
        - auto.
        - erewrite <- map_length. instantiate (1:=t0).
          simpl in Hsetvariables'. rewrite Hsetvariables'. eapply map_length.
        - apply Hb''.
        - unfold variable_extraction in H1. simpl in H1. Search remove_dup.
          erewrite remove_dup_equals_incl in H1. Search incl. eapply incl_app_inv in H1. destruct H1.
          apply H3. }
       destruct H3. rewrite H3 in Hb''. (*5/26/23*)
       exists x.
       split.
       --- unfold hoare_triple in IHc.
           eapply IHc; auto.
           5 : { apply Hstate. }
           4 : apply H2.
           3 : { simpl in H1. Search variable_extraction. eapply incl_equals in H1. simpl in H1. Search incl.
                 eapply incl_app_inv in H1. destruct H1. eapply incl_equals. apply H4. }
           2 : { exists (S n). apply Hb''. }
           simpl. simpl in Hsetvariables'. rewrite Hsetvariables'.
           erewrite needed_for_reduce_again; eauto. rewrite <- Hsetvariables'. erewrite map_length. auto.
       --- erewrite token_update_vars in Whileworks. 
           rewrite need_for_fst in Whileworks. rewrite need_for_snd in Whileworks.
           rewrite need_for_snd in Hsetvariables'. rewrite H3 in Whileworks. (*5/28/23*)
           unfold token_update in Whileworks. rewrite need_for_fst in Whileworks.
           rewrite need_for_snd in Whileworks.
           exists (t, t_update_list t0 X (map Number x)).
           split.
           ---- simpl. rewrite needed_for_reduce_again; eauto. erewrite map_length. Search eval length.
                eapply extract_fun_same_lengths; auto.
                3 : { apply Hb''. }
                + instantiate (1:=v0). erewrite <- map_length. rewrite Hsetvariables'. erewrite map_length. auto.
                + simpl. rewrite Hsetvariables'. erewrite needed_for_reduce_again; eauto. rewrite <- Hsetvariables'.
                  erewrite map_length. auto.
           ---- exists (S (S n)). rewrite eval_eq. rewrite eval_eq. rewrite eval_eq.
                erewrite token_update_list_function_vars. rewrite ! need_for_fst. rewrite ! need_for_snd.
                erewrite map_over_tokens_vars. pose proof (closed_env <{while b do c end}> 
                (t, t0) X (Some (FunctionToken "Whilefun"))
                (map VariableToken X) 
                (If
                 (Application
                    (Lambda (map VariableToken X)
                       (bimp_to_functional b))
                    (Vars (map VariableToken X)))
                 (Application
                    (Vars (cons (FunctionToken "Whilefun") nil))
                    (Application (extract_fun c X)
                       (Vars (map VariableToken X))))
                 (Vars (map VariableToken X))) (t, t0) (S n)).
                specialize (H4 H1). specialize (H4 H). remember (S n) as m in H4. 
                simpl in H4. rewrite Heqm in H4 at 1. simpl eval in H4.
                specialize (H4 E). remember (t, t0) as env1 in H4.
                specialize (H4 (t, t_update_list t0 X (map Number x))). 
                destruct H4. rewrite Heqm in H4 at 1. simpl in H4. destruct H4.
                specialize (H5 (map Number x)).
                erewrite ! token_update_vars in H5. simpl in H5. rewrite Heqenv1 in H5.
                simpl in H5. injection H4 as H4. rewrite <- H4 in H5. simpl in H5.
                erewrite needed_for_reduce_again; eauto.
                2 : { erewrite map_length. eapply extract_fun_same_lengths; auto.
                      - instantiate (1:=v0). erewrite <- map_length. rewrite Hsetvariables'.
                        erewrite map_length. auto.
                      - instantiate (1:=(pair
               (t_update t "Whilefun"
                  (Closure (Some (FunctionToken "Whilefun"))
                     (map VariableToken X)
                     (If
                        (Application
                           (Lambda (map VariableToken X)
                              (bimp_to_functional b))
                           (Vars (map VariableToken X)))
                        (Application
                           (Vars
                              (map FunctionToken
                                 (cons "Whilefun" nil)))
                           (Application (extract_fun c X)
                              (Vars (map VariableToken X))))
                        (Vars (map VariableToken X)))
                     (pair t t0)))
               (t_update_list t0 X (map t0 X)))). simpl. erewrite needed_for_reduce_again; eauto. symmetry.
                        eapply map_length.
                      - apply Hb''. }
                assert (Datatypes.length (map VariableToken X) =
                Datatypes.length (map Number x)).
                { erewrite ! map_length.  eapply extract_fun_same_lengths; auto.
                      - instantiate (1:=v0). erewrite <- map_length. rewrite Hsetvariables'.
                        erewrite map_length. auto.
                      - instantiate (1:=(pair
               (t_update t "Whilefun"
                  (Closure (Some (FunctionToken "Whilefun"))
                     (map VariableToken X)
                     (If
                        (Application
                           (Lambda (map VariableToken X)
                              (bimp_to_functional b))
                           (Vars (map VariableToken X)))
                        (Application
                           (Vars
                              (map FunctionToken
                                 (cons "Whilefun" nil)))
                           (Application (extract_fun c X)
                              (Vars (map VariableToken X))))
                        (Vars (map VariableToken X)))
                     (pair t t0)))
               (t_update_list t0 X (map t0 X)))). simpl. erewrite needed_for_reduce_again; eauto. symmetry.
                        eapply map_length.
                      - apply Hb''. }
                specialize (H5 H6). rewrite Heqm in H5. rewrite <- H5. apply Whileworks.
    -- unfold "->>". intros. exists v.
       split.
       --- apply H2.
       --- exists env. split; auto.
    -- unfold "->>". simpl extract_fun. unfold Whilefun. unfold hoare_triple.
       intros. destruct H2 as ((v0 & (Hstate & (env0 & Hsetvariables' & (n & Whileworks)))) & Hb).
       destruct n; try discriminate. simpl in Whileworks.
       destruct (eval env0
                   (Rec (FunctionToken "Whilefun") (map VariableToken X)
                      (If
                         (Application (Lambda (map VariableToken X) (bimp_to_functional b))
                            (Vars (map VariableToken X)))
                         (Application (Vars (cons (FunctionToken "Whilefun") nil))
                            (Application (extract_fun c X) (Vars (map VariableToken X))))
                         (Vars (map VariableToken X)))) n) eqn : E; try discriminate.
       destruct l; try discriminate.
       destruct v1; try discriminate.
       destruct l; try discriminate.
       destruct (eval env0 (Vars (map VariableToken X)) n) eqn : E1; try discriminate.
       destruct n; try discriminate. simpl in E. inversion E. subst.
       simpl in Whileworks. erewrite token_update_vars in Whileworks. erewrite ! need_for_fst in Whileworks.
       erewrite ! need_for_snd in Whileworks. simpl in E1. destruct env1 eqn : Hfstsnd.
       erewrite map_over_tokens_vars in E1. injection E1 as E1. simpl in Whileworks.
       destruct (eval) eqn : Hb'; try discriminate.
       destruct l0; try discriminate. destruct v1; try discriminate.
       destruct l0; try (destruct b0; discriminate). assert (b0 = false).
       { unfold bassn in Hb. Search not true. eapply not_true_is_false in Hb. rewrite <- Hb. symmetry. 
         destruct n in Hb'; try discriminate. simpl in Hb'.
         destruct n in Hb'; try discriminate. rewrite eval_eq in Hb'. remember (S n) as m in Hb'.
         rewrite Heqm in Hb' at 1. simpl in Hb'.
         erewrite token_update_vars in Hb'. erewrite need_for_fst in Hb'.
         erewrite need_for_snd in Hb'. erewrite map_over_tokens_vars in Hb'. 
         erewrite needed_for_reduce_again in Hb'; eauto. 2 : { rewrite <- E1. symmetry. eapply map_length. }
         eapply eval_bool; auto.
         5 : apply Hb'. instantiate (2:=X). instantiate (1:=v0).
         - simpl. erewrite two_updates. simpl in Hsetvariables'. rewrite Hsetvariables' in E1.
           rewrite E1. eapply needed_for_reduce_again; eauto. rewrite <- E1. rewrite <- Hsetvariables'.
           symmetry. eapply map_length.
         - Search variable_extraction. eapply incl_equals in H1. simpl in H1.
           Search incl. eapply incl_app_inv in H1. destruct H1. apply H1.
         - symmetry. erewrite <- map_length. instantiate (1:=Number). symmetry.
           erewrite <- map_length. simpl in Hsetvariables'. instantiate (1:=t0).
           rewrite <- Hsetvariables'. auto.
         - apply Hstate.
         - apply H. } subst.
       destruct n; try discriminate. simpl in Whileworks. injection Whileworks as Whileworks.
       erewrite map_over_tokens_vars in Whileworks. erewrite needed_for_reduce_again in Whileworks; eauto.
       --- simpl in Hsetvariables'. rewrite Hsetvariables' in Whileworks.
           eapply unfold_map_Number in Whileworks. subst. apply Hstate.
       --- symmetry. eapply map_length. Unshelve.
           + exact (fst env). + exact 0. + exact x3.
Qed.


(*
eval r1 (extract_fun c X) n = Some [Closure a b c d1] -> forall r2, exists d2, eval r2 (extract_fun c X) n =
Some [Closure a b c d2] /\ forall v, eval (t_update_list d1 b v) c = eval (t_update_list d2 b v) c.
*)

(*
(\x.(x x)) (\x. (x x))
Closure x (x x) {}, Closure x (x x) {} 
eval ((x x) {x = Closure x (x x) {}})

(\x.(\y.x)) (\x.y)
Closure x (\y.x) {}, Closure x y {}
eval (\y.x {x = Closure x y {}})
Closure y x {x = Closure x y {}}
*)

(* \ ["y"; "x"]
       . (Rec "Whilefun" ["y"; "x"]
            (If ((Less (Num 0) (Vars ["x"])))
               ((Vars ["Whilefun"])
                ((\ ["y"; "x"]
                  . (\ ["y"; "x"] . Let "x" (Minus (Vars ["x"]) (Num 1)) ["y"; "x"])
                    ((Let "y" (Mult (Vars ["x"]) (Vars ["y"])) ["y"; "x"])))
                 (Vars ["y"; "x"]))) (Vars ["y"; "x"])))
         ((Let "y" (Num 1) ["y"; "x"]))
     : function
*)


(* { P } c { Q }

c : com
P, Q : assertion

state := var -> value

(* shallow embedding *)
assertion := state -> Prop

(x > 3) holds on s iff s(x) > 3

(* deep embedding *)
Inductive assertion : Type :=
| VarEq (v : var) (n : nat)
| AndAssert (a1 a2 : assertion)
| ...
.

Fixpoint assertion_hold (a : assertion) (s : state) :=
match a with
| VarEq v n => s(v) = n
| AndAssert a1 a2 => assertion_hold a1 s /\ assertion_hold a2 s
| ...
end.

(* target-specific shallow embedding *)
assertion := list nat -> list nat
(or (string -> nat) -> (string -> nat) ) (or use maps from Maps.v in LF)

(fun r => (nth 0 r + nth 1 r, 3)) represents the assertion (var_x, var_y) = (x + y, 3)

{ id } c { Q } means "if we start with initial values r0 and then run c,
  we end with variables having values Q(r0)."

Fixpoint extract_fun (c : com) : assertion :=
  match c with
  | CAsgn x a => (fun r => eval a r :: tl r) (* only when x is the first var *)


(* target-specific deep embedding *)
Inductive assertion :=
| VarEq (r : list var) (f : list nat -> list nat).

VarEq [x; y] (fun r => [nth 0 r + nth 1 r; 3]) represents {(x, y) = (x + y, 3)}

*)
