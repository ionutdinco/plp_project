
Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Delimit Scope string_scope with string.
Local Open Scope list_scope.
Require Import List.
Import ListNotations.


Inductive ErrorNat :=
| error_nat : ErrorNat
| num : nat -> ErrorNat.

Inductive ErrorBool :=
| error_bool : ErrorBool
| boolean : bool -> ErrorBool.



Inductive StringExp :=
| svar : string -> StringExp
| sstring : string -> StringExp
| concat: StringExp -> StringExp -> StringExp
| compare: StringExp -> StringExp -> StringExp
| substring: StringExp -> StringExp -> StringExp.


Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| alength: string -> AExp.


Inductive BExp :=
| berror
| btrue : BExp
| bfalse : BExp
| bvar: string -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.


Coercion svar: string >-> StringExp.
Notation "A += B" := (concat A B) (at level 60).
Notation " A ?? B" := (compare A B) (at level 60).
Notation "len( A )" := (alength A)(at level 50).
Notation "A <- B" := (substring A B)(at level 55). 


Definition Parametrii := list string.
Inductive Stmt :=
| vect_decl : string -> nat ->nat->Stmt
| nat_decl : string -> Stmt
| nat_assign : string -> AExp -> Stmt
| nat_decl_assign : string -> AExp -> Stmt
| string_decl : string -> Stmt
| string_assign : string -> string -> Stmt
| string_decl_assign : string -> string -> Stmt
| bool_decl : string -> Stmt
| bool_assign : string -> BExp -> Stmt
| bool_decl_assign : string -> BExp -> Stmt
| variabila_assign : string -> string ->Stmt
| apelare_functie : string -> Parametrii -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt 
| ifthen : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt ->Stmt
| for_each : string -> string -> nat -> Stmt-> Stmt
| comentarii : Stmt -> Stmt
| Caz : ErrorNat ->Stmt -> Stmt
| switch_case : AExp -> Stmt -> Stmt
| switch : AExp -> AExp -> Stmt -> AExp ->Stmt -> Stmt -> Stmt
| break : Stmt -> Stmt
| Concat_str : string -> string -> Stmt.

Inductive ValuesType :=
| err_undecl : ValuesType
| err_assign : ValuesType
| default : ValuesType
| res_nat: ErrorNat -> ValuesType
| res_bool: ErrorBool -> ValuesType
| res_string : string -> ValuesType
| codebody : Stmt -> ValuesType.   


Coercion codebody : Stmt >-> ValuesType.

Inductive Body :=
| decl_functie : string -> Parametrii -> Stmt -> Body
| decl_globale: string -> Body
| decl_functie_main : Stmt -> Body
| seq_program : Body -> Body -> Body.



Coercion avar :  string >-> AExp.
Coercion anum : nat >-> AExp.
Coercion num : nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.


Notation "A +' B" := (aplus A B) (at level 48).
Notation "A ++' " := (aplus A 1) (at level 48).
Notation "A -' B" := (aminus A B) (at level 48).
Notation "A --' " := (aminus A 1) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 58).
Notation "A %' B" := (amod A B) (at level 58).
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A =>' B" := (bgreaterthan A B) (at level 53).
Notation "A ==' B" := (bequal A B) (at level 53).
Notation " !' A" := (bnot A) (at level 53).
Notation "A &' B" := (band A B) (at level 53).
Notation "A |' B" := (bor A B) (at level 53).
Notation "'iVect' X [[ n ]] " := (vect_decl X n 1) (at level 90).
Notation "'bVect' X [[ n ]] " := (vect_decl X n 2) (at level 90).
Notation "'sVect' X [[ n ]] " := (vect_decl X n 3) (at level 90).
Notation " 'int' A " := (nat_decl A) (at level 50).
Notation " X ':int=' A  " := (nat_assign X A) (at level 90).
Notation " 'd_int' X '::i=' A  " := (nat_decl_assign X A) (at level 90).
Notation " 'boll' A " := (bool_decl A) (at level 50).
Notation " X ':boll=' A  " := (bool_assign X A) (at level 90).
Notation " 'd_boll' X '::b=' A  " := (bool_decl_assign X A) (at level 90).
Notation " 'd_string' X '::st=' A  " := (string_decl_assign X A) (at level 90).
Notation " 'sstring' A " := (string_decl A) (at level 50).
Notation " X ':string=' A  " := (string_assign X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation " 'If1' '(' b ')' 'Then' { S1 } " := (ifthen b S1 ) (at level 97).
Notation " 'If' '(' b ')' 'Then' { S1 } 'Else' { S2 }  " := (ifelse b S1 S2 ) (at level 97).
Notation " 'While*' '(' b ')' '{' S '}' " := (while b S)(at level 97).
Notation "'For'  ( V , it , n )  { S }" := (for_each V it n S) (at level 94).
Notation " 'Do' '{' S1 '}' 'while*' '(' b ')' " := ( S1 ;; while b (S1) ) (at level 97).
Notation " 'function' S1 '(' a ')' '{' S2 '}' " :=( decl_functie S1 a S2)(at level 45).
Notation " 'int_main()' ( S2 ) " :=( decl_functie_main S2).
Notation " 'decl_global' A " := (decl_globale A) (at level 50).
Notation " S1 ';*' S2 " := (seq_program S1 S2)(at level 50).
Notation " /* s *\ " := (comentarii s ) (at level 48).
Notation " 'Switch' '(' v ')' '{' 'case' a1 ':' s1 'case' a2 ':' s2 s3 } " := (switch v a1 s1 a2 s2 s3) (at level 50).
Notation "'Case' ( A ) {' S '} " := (Caz A S) (at level 95).
Notation "'Switch2' ( A ) : [{ S }] " := (switch_case A S) ( at level 93).

Check switch ("v") 3 ("a":int=4) 
                   4 ("a":int=3)
                     ("a":int=3) .
Check While* ( "i" =>' 9 ) { "ok" :int= "dada" } .
Check "k"++'.
Check 1+'1.
Check decl_functie "da" [ "ok";"da" ] ("ok":int= "ok"++') .
Check decl_functie_main ( "ok":int= "ok"++' ).
Check int "a".
Check "a":int=3.
Check  
      decl_functie "da" [ "ok";"da" ] ("ok":int= "ok"++') ;*
      decl_global "ok" ;*
      decl_functie_main ( ( "ok":int="ok"+'1) ;;

                          Do { 
                              "ok":int="ok"+'1
                          }while* ( "ok" =>' 0);;
                          apelare_functie "da" [ "a";"b" ]
                        ).


Definition check_eq_over_types (t1 : ValuesType)(t2 : ValuesType) : bool :=
  match t1 with
| err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
| err_undecl => match t2 with 
                   | err_undecl => true
                   | _ => false
                   end
| default => match t2 with 
                   | default => true
                   | _ => false
                   end
| res_nat n=> match t2 with 
                   | res_nat n=> true
                   | _ => false
                   end
| res_bool n=> match t2 with 
                   | res_bool n=> true
                   | _ => false
                   end
| res_string n=> match t2 with 
                   | res_string n=> true
                   | _ => false
                   end
| codebody c1 => match t2 with 
                     | codebody c2 => true 
                     | _ => false 
                     end
  end.

Definition Env := string -> ValuesType.
Definition env1 : Env := fun x => err_undecl.


Definition update (env : Env) (x : string) ( v : ValuesType ) : Env :=
fun y =>
 if(string_beq x y)
  then 
      if ( andb (check_eq_over_types (env y) err_assign ) true )
                       then v
         else if (andb ( check_eq_over_types (env y) v) true ) then v else
            if (andb (check_eq_over_types (env y) default) true ) then v else err_assign
  else (env y).

Definition plus_eroareNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 =>  (v1 + v2)
    end.

Definition min_eroareNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else  (n1 - n2)
    end.

Definition mul_eroareNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 =>  (v1 * v2)
    end.

Definition div_eroareNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 =>  (Nat.div v1 v2)
    end.

Definition mod_eroareNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => (v1 - v2 * (Nat.div v1 v2))
    end.

Fixpoint Calcul_Lungime (s1 : string) : nat :=
 match s1 with
 | EmptyString =>0
 | String c s1' => S (Calcul_Lungime s1')
end.

Definition length_errorNat (r:ValuesType) : ErrorNat :=
match r with
 | res_string s => Calcul_Lungime s
 | _ =>0
end.


Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
                end
  | anum v => num v
  | aplus a1 a2 => (plus_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | aminus a1 a2 => (min_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_eroareNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | alength a1 => (length_errorNat (env a1 ) )
  end.
Reserved Notation "A =[ S ]=> N" (at level 70).
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> num n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_eroareNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_eroareNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (min_eroareNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_eroareNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_eroareNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Definition env : Env := fun x => err_undecl.

Compute aeval (1+'5) env error_nat.
 
Example substract_error : 909 -' 4588 =[ env ]=> error_nat.
Proof.
  eapply substract. 
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.
Example add1 : 109 +' 575 =[ env ]=> 684.
Proof.
    eapply add.
      -eapply const.
      -eapply const.
      - simpl. reflexivity.
Qed.

Require Import Nat.
Definition lt_eroareBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => ( leb v1 v2 )
    end.
Compute lt_eroareBool 3 4.
Definition gt_eroareBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => (Nat.ltb v2 v1)
    end.

Definition eq_eroareBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 =>  (Nat.eqb v2 v1)
    end.
Definition not_eroareBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v =>  (negb v)
    end.

Definition and_eroareBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 =>(andb v1 v2)
    end.

Definition or_eroareBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 =>  (orb v1 v2)
    end.
Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
  | btrue => boolean true
  | bfalse => boolean false
  | berror => error_bool
  | bvar v => match (env v) with
                | res_bool n => n
                | _ => error_bool
                end
  | blessthan a1 a2 => (lt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bgreaterthan a1 a2 => (gt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bequal a1 a2 => (gt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_eroareBool (beval_fun b1 envnat))
  | band b1 b2 => (and_eroareBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_eroareBool (beval_fun b1 envnat) (beval_fun b2 envnat))
end.

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=>  true
| b_false : forall sigma, bfalse ={ sigma }=>  false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | res_bool x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_eroareBool i1 i2) ->
    a1 <=' a2 ={ sigma }=> b
| b_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gt_eroareBool i1 i2) ->
    a1 =>' a2 ={ sigma }=> b
| b_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (eq_eroareBool i1 i2) ->
    a1 ==' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_eroareBool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_eroareBool i1 i2) ->
    (a1 &' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_eroareBool i1 i2) ->
    (a1 |' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').
Example boolean_operation : bnot (100 <=' "n") ={ env }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition fun_strConcat (s1 s2: string) : string :=
match s1 , s2 with 
  | str1,  str2 =>  (str1 ++ str2)
end.


Definition concat_ErrorString (s1 s2 : string) : string := 
match s1, s2 with
|  s1',  s2' =>  ( fun_strConcat s1' s2' )
end.
 

Reserved Notation "STR '=S[' St ']S>' N" (at level 60). 
Inductive seval : StringExp -> Env -> string -> Prop :=
| s_string : forall s n sigma,  s =S[ sigma ]S>  n
| s_var : forall s sigma, svar s =S[ sigma ]S> match (sigma s) with
                                                | res_string s => s
                                                | _ => "error_string"
                                                end
| s_concat : forall s1 s2 sigma s st1 st2,
    s1 =S[ sigma ]S> st1 ->
    s2 =S[ sigma ]S> st2 ->
    s = concat_ErrorString st1 st2 ->
     s1 += s2  =S[ sigma ]S> s

 
where "STR '=S[' St ']S>' N" := (seval STR St N).


Definition update_list_globale ( L : list string ) ( x : string )
    : list string := L++ [x].
Definition update_list_locale ( L : list string ) ( x : string )
    : list string := L++ [x].
Definition update_list_functii ( L : list string ) ( x : string )  
    : list string := L++ [x].

Compute update_list_globale ["a";"b"] "c".  
Definition parametrii1 := Parametrii.
Definition parametrii2 := Parametrii.


Fixpoint Concat (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (Concat s1' s2)
  end.


Definition to_char (n: nat) : string :=
 match n with
  | 0 =>"0"
  | 1 =>"1"
  | 2 =>"2"
  | 3 =>"3"
  | 4 =>"4"
  | 5 =>"5"
  | 6 =>"6"
  | 7 =>"7"
  | 8 =>"8"
  | 9 =>"9"
  | _ =>"0"

 end.
 
Definition vect_concat (s1 :string) (n:nat) : string :=
 Concat (Concat (Concat s1 "[") (to_char n)) "]".

Definition Verifica_Rezultat (n: nat) : ValuesType :=
match n with
 | 1 => res_nat 0 
 | 2 => res_bool true
 | 3 => res_string "" 
 | _ => default
end.

Fixpoint decl_vect (env : Env) (s : string) (nr_elemente tip_elemente: nat) : Env :=
 match nr_elemente with
  | 0 => env
  | S n'=> decl_vect (update (update env (vect_concat s n') default) (vect_concat s n') (Verifica_Rezultat tip_elemente) ) s n' tip_elemente
 end.


 

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (nat_assign x a) -{ sigma }-> sigma'
| e_nat_decl: forall x sigma sigma',
    sigma' = (update sigma x err_assign) ->
    (nat_decl x) -{ sigma }-> sigma'
| e_nat_decl_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (nat_decl_assign x a) -{ sigma }-> sigma'
| e_bool_decl: forall x sigma sigma',
   sigma' = (update sigma x err_undecl) ->
   (bool_decl x) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (bool_assign x a) -{ sigma }-> sigma'
| e_bool_decl_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (bool_decl_assign x a) -{ sigma }-> sigma'
| e_string_assign: forall a i x sigma sigma',
   sigma' = (update sigma x (res_string i)) ->
   (string_assign x a) -{ sigma }-> sigma'
| e_string_decl: forall x sigma sigma',
    sigma' = (update sigma x err_assign) ->
    (string_decl x) -{ sigma }-> sigma'
| e_string_decl_assign: forall a i x sigma sigma',
   sigma' = (update sigma x (res_string i)) ->
   (string_decl_assign x a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=>true ->
    s1 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma'  
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> boolean false ->
    s2 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma' 
| e_switch1 : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s1 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_switch2 : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s2 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_switchDefault : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s3 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=>  true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_apelare : forall x parametrii1 sigma1 sigma2,
    (apelare_functie x parametrii1) -{ sigma1 }-> sigma2
| e_coments : forall s sigma1 sigma2 ,
    /* s *\ -{ sigma1 }-> sigma2
| e_break : forall s sigma1 sigma2 ,
    (break s ) -{ sigma1 }-> sigma2
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Reserved Notation "S -*{ Sigma }*-> Sigma'" (at level 60).
Inductive Evaluare_Body : Body -> Env -> Env -> Prop :=
| e_decl_global: forall x list_glb' list_glb sigma sigma',
    sigma' = (update sigma x (res_nat (num 0))) ->
    list_glb' = (update_list_globale list_glb x) ->
    (decl_globale x) -*{ sigma }*-> sigma'
| e_decl_functie: forall x s parametrii2    sigma sigma',
    s -{ sigma }-> sigma' ->
    (decl_functie x parametrii2 s ) -*{ sigma }*-> sigma'
| e_decl_functie_main : forall s sigma sigma',
    s -{ sigma }-> sigma' ->
    (decl_functie_main s ) -*{ sigma }*-> sigma'
| e_seq_prg : forall s1 s2 sigma sigma1 sigma2,
    s1 -*{ sigma }*-> sigma1 ->
    s2 -*{ sigma1 }*-> sigma2 ->
    (s1 ;* s2) -*{ sigma }*-> sigma2
where "s -*{ sigma }*-> sigma'" := (Evaluare_Body s sigma sigma').


Scheme Equality for ErrorNat.

Definition env_sprijin : Env := fun x => err_undecl.

Definition Concat_res (r1 r2 :ValuesType) :ValuesType :=
match r1,r2 with
| res_string s1, res_string s2 => res_string (Concat s1 s2)
| _,_ => err_assign
end. 
  
Fixpoint Evaluare_Program (s : Stmt) (env : Env) (nr_iteratii: nat) : Env :=
    match nr_iteratii with
    | 0 => env
    | S nr_iteratii' => match s with
                | sequence S1 S2 => Evaluare_Program S2 (Evaluare_Program S1 env nr_iteratii' ) nr_iteratii'
                | nat_decl a => update (update env a default) a (res_nat 0)
                | bool_decl b => update (update env b default) b (res_bool true)
                | string_decl s => update env s default 
                | vect_decl s n m=> decl_vect env s n m
                | nat_assign a aexp => update env a (res_nat (aeval_fun aexp env))
                | bool_assign b bexp => update env b (res_bool (beval_fun bexp env))
                | string_assign s str => update env s (res_string str)
                | nat_decl_assign a valoare => update (update env a default) a (res_nat (aeval_fun valoare env))
                | string_decl_assign a valoare => update (update env a default) a (res_string valoare)
                | bool_decl_assign a valoare => update (update env a default) a (res_bool (beval_fun valoare env))
                | variabila_assign s1 s2 =>if(check_eq_over_types (env s1) (env s2))
                                     then update env s1 (env s2) 
                                     else env
                | ifthen cond s' => 
                    match (beval_fun cond env) with
                    | error_bool => env
                    | boolean v => match v with 
                                 | true => Evaluare_Program s' env nr_iteratii'
                                 | false => env
                                 end
                    end
                | ifelse cond S1 S2 => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => Evaluare_Program S1 env nr_iteratii'
                                 | false => Evaluare_Program S2 env nr_iteratii'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond env) with 
                        | error_bool => env
                        | boolean v => match v with
                                     | true => Evaluare_Program (s' ;; (while cond s')) env nr_iteratii'
                                     | false => env
                                     end
                        end
                | Caz n St =>Evaluare_Program St env nr_iteratii'
                
                | switch_case AE C =>
                                 match C with
                                         | Caz n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                       then Evaluare_Program St env nr_iteratii'
                                                        else env
                                          | sequence S1 S2 => match S1 with    
                                                              | Caz n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                                            then Evaluare_Program St env nr_iteratii'   
                                                                            else Evaluare_Program (switch_case AE S2) env nr_iteratii'
                                                               | _ => env
                                                                end
                                         | _ => env
                                 end
                | for_each V it n St=>
                                  match n with 
                                      | 0 => Evaluare_Program St (update env it (env (vect_concat V 0))) nr_iteratii'
                                      | S n' => Evaluare_Program (St ;; for_each V it n' St) (update env it (env (vect_concat V n))) nr_iteratii'
                                      end
                 | Concat_str S1 S2 => update env S1 (Concat_res (env S1) (env S2))
                 | _ => env_sprijin               
                end
    end.



Definition Exemple_1:=
 int "a";;
 ("a" :int=59);;
 If1 ("a" <=' 7 ) Then { "a" :int= 10 }.

Compute (Evaluare_Program Exemple_1 env 100) "a".

Definition Exemple_2 :=
 int "a" ;; int "b" ;; 
 ("a":int= 5) ;; 
 ("b" :int= 2) ;; 
  (d_int "c" ::i= "a" +' "b");;
  (d_int "d" ::i= "a" -' "b");;
  (d_int "e" ::i= "a" *' "b");;
  (d_int "f" ::i= "a" /' "b").

Compute (Evaluare_Program Exemple_2 env 100) "f".

Definition Exemple_3 :=
 sstring "a" ;; 
 sstring "b" ;; 
 ("a":string= "alt") ;; 
 ("b" :string= "ceva") ;; 
  Concat_str "a" "b".    

Compute (Evaluare_Program Exemple_3 env 100) "a" .

 
Definition Test :=
iVect "x" [[ 8 ]] ;;
 ("x[7]" :int=1);;
 ("x[6]" :int=2);; 
 ("x[5]" :int=3);;
 ("x[4]" :int=4);;
 ("x[3]" :int=5);;
 ("x[2]" :int=6);;
 ("x[1]" :int=7);;
 ("x[0]" :int=8);;
 int "it" ;;
 int "sum" ;;
 ("sum" :int=0) ;;
 For ("x" , "it" , 3 )  { ("sum" :int= "sum" +' "it") }.
 
   
Compute (Evaluare_Program Test env 100) "sum".

Definition Checkq :=
int "a" ;;
int "b" ;; 
("a" :int= 3 +' 12) ;;
Switch2 ("a" ) : [{
Case (2) {' ("b" :int= 2) '} ;;
Case (7) {' ("b" :int= 7) '} ;;
Case (15) {' ("b" :int= 15) '}
}].

Compute (Evaluare_Program Checkq env 100) "b". 

Definition ex_stmt :=  
  int "i";;  
  int "j";;
  int "s";; 
  ("i":int=0);;
  ("j":int=1);;
 
  
  ifthen ( "i" <=' "j") 
    (("s":int=18);;

    break
    (("s" :int= 11);;
     ("s" :int= 12) ) );;
   
  boll "c";;
  ("c" :boll= btrue);;

  /* "s":int=19 *\;;

  While* (3 <=' 2) { ("s" :int= "s" +' 10)} .

Example eval_ex : 
  exists state, ex_stmt -{ env }-> state .
Proof.
  eexists.
  +unfold ex_stmt.
    eapply e_seq.
      -eapply e_seq.  
        -- eapply e_seq.
          --- eapply e_seq.  
             ++ eapply e_seq.
              +++ eapply e_seq. 
               ++++ eapply e_seq.
                +++++ eapply e_seq.  
                 ++++++ eapply e_seq.     
                  +++++++ eapply e_nat_decl. eauto.
                  +++++++ eapply e_nat_decl. eauto.
                  ++++++ eapply e_nat_decl; eauto.
            +++++ eapply e_nat_assign. 
              ++++++ eapply const.
              ++++++ split.
         ++++ eapply e_nat_assign.
           +++++ eapply const.
           +++++ split.
       +++ eapply e_if_then.
           ++++ eapply b_lessthan.
             +++++++ eapply var. 
             +++++++ eapply var.
             +++++++ simpl. reflexivity.
          ++++ eapply e_seq.
            +++++++ eapply e_nat_assign. eapply const. eauto.
            +++++++ eapply e_break.
  ++ eapply e_bool_decl. split.
  --- eapply e_bool_assign.
    ++ eapply b_true.
    ++ split.
    -- eapply e_coments. 
  -eapply e_whilefalse.
   ++ eapply b_lessthan.
    +++ eapply const. 
    +++ eapply const.
    +++ simpl. reflexivity.    
  
Abort.


Definition max1 :=
  decl_global "n";*
  decl_functie "functie_exempl" [ "ok";"da" ]  ("ok":int=3)  ;*
  decl_global "ok" ;*
  int_main() ( (int "aux1") ;;
                       ("aux1" :int=3 );;
                       ifthen ("aux1"=='3) ("aux1":int=7);;
                       apelare_functie "functie_exempl" [ "aux1";"b" ]
                       ).

Definition state0 := fun (x:string) => err_undecl.
Example eval_max1 : 
 exists state, max1 -*{ state0 }*-> state .
Proof.
  eexists.
  - unfold max1. 
    eapply e_seq_prg.
    ++ eapply e_seq_prg.
        +++ eapply e_decl_global;eauto.
        +++ eapply e_decl_functie; eauto.
             +++++ eapply e_nat_assign.
              ++++++ eapply const.
              ++++++ split.
    ++ eapply e_seq_prg.
      +++ simpl. eapply e_decl_global; eauto.
      +++ eapply e_decl_functie_main. 
          eapply e_seq.
          ++++ eapply e_seq.
            +++++ eapply e_seq.
              +++++++ eapply e_nat_decl.
                ++++++++ simpl. split. 
              +++++++ eapply e_nat_assign.
                    ---- eapply const.
                    ---- split.
             +++++ eapply e_if_then.
               ++++++ eapply b_equal.
                +++++++ eapply var.
                +++++++ eapply const.
                +++++++ simpl. reflexivity.
                  ++++++ eapply e_nat_assign.
                    +++++++ eapply const.
                    +++++++ split.
            ++++ eapply e_apelare.   
Abort.
