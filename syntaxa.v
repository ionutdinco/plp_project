
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
| error_string : ErrorString
| String : string -> ErrorString.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion String : string >-> ErrorString.
 
(*  AExp *)
Inductive AExp :=
  | avar: string -> AExp 
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp 
  | adiv: AExp -> AExp -> AExp 
  | amod: AExp -> AExp -> AExp. 

Coercion avar : string >-> AExp.
Coercion anum : ErrorNat >-> AExp.

(*  BExp *)
Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bgt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Coercion bvar : string >-> BExp.

Inductive StringExp :=
| svar : string -> StringExp
| sstring : ErrorString -> StringExp
| concat: ErrorString -> ErrorString -> StringExp
| compare: ErrorString -> ErrorString -> StringExp
| slength: ErrorString -> StringExp
| substring: ErrorString -> ErrorString -> StringExp.

Coercion svar: string >->StringExp.
Notation " A += B " := (concat A B) (at level 60).
Notation " A ?? B" := (compare A B) (at level 60).
Notation "len( A )" := (slength A)(at level 50).
Notation "A <- B" := (substring A B)(at level 55).
Check "ionut" += "dinco".
Check "ana"??"Ana".
Check len("ceva").
Check "in" <- "maine".

Inductive Pointer := 
| nullptr : Pointer
| ptr : ErrorString -> Pointer
| ref : ErrorString -> Pointer.
Scheme Equality for Pointer.

Notation " A **" := (ptr A)(at level 20).
Notation "&& A" := (ref A )(at level 20).
Check "a"**.
Check &&"a".

(*Tablouri*)

Inductive ArrayExp :=
| elementAt : ErrorString -> nat -> ArrayExp
| get_element_at : ErrorString -> nat -> ArrayExp
| deleteAt : ErrorString -> nat -> ArrayExp.

Notation " s [[' i ']] " := (elementAt s i)(at level 22).
Notation " t [[[' i ']]]? " := (get_element_at t i)(at level 22).
Check "a"[['1']].
Check "a"[[['1']]]?.

(*Statements*)
Require Import Coq.Lists.List.
Import ListNotations.
Scheme Equality for list.


(*  Stmt *)
Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt 
  | bool_decl: string -> BExp -> Stmt 
  | string_decl: string -> StringExp -> Stmt
  | array_decl: string -> nat -> Stmt
  | array_decl_list_of_nat: string -> nat -> list nat ->Stmt
  | array_decl_list_of_bool: string -> nat -> list bool ->Stmt
  | array_decl_list_of_string: string -> nat -> list string ->Stmt
  | pointer_decl_nat : string -> Pointer -> Stmt
  | pointer_decl_bool: string -> Pointer -> Stmt
  | reference_decl : string -> string -> Stmt
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | string_assign : string -> StringExp -> Stmt
  | pointer_assign : string -> Pointer -> Stmt
  | reference_assign : string -> string -> Stmt
  | array_elm_assign_nat : ArrayExp -> ErrorNat -> Stmt
  | array_elm_assign_bool : ArrayExp -> ErrorBool -> Stmt
  | array_elm_assign_string : ArrayExp -> ErrorString -> Stmt
  | array_elm_output_nat : ArrayExp -> Stmt
  | citeste : string -> Stmt (*citeste inputul si il pune intr-o variabila*)
  | scrie : StringExp -> Stmt (*scrie un string*)
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | fors : Stmt -> BExp -> Stmt -> Stmt
  | switch : AExp -> list cases -> Stmt
  | functionCall: string -> list string -> Stmt
   with cases  :=
   | case : AExp -> Stmt -> cases
   | defaultcase: Stmt->cases.


(* Notatii *)

(* operatii aritmetice *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

(* operatii binare*)
Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

(* notatii stmt *)
Notation "X :nat= A" := (nat_assign X A)(at level 90).
Notation "X :bl= A" := (bool_assign X A)(at level 90).
Notation "X :stg= A" := (string_assign X A)(at level 90).
Notation "'dNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'dBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'dStg' X ::= A" := (string_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'while' ( B ) 'do' { S }" := (while B S) (at level 97).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "A [[ B ]]" := (array_decl  A B) (at level 58).
Notation "A [[ B ]] :lnat= C" := (array_decl_list_of_nat A B C) (at level 58). 
Notation "A [[ B ]] :lbool= C" := (array_decl_list_of_bool A B C) (at level 58). 
Notation "A [[ B ]] :lstg= C" := (array_decl_list_of_string A B C) (at level 58).
Notation "A [[ B ]]?nat" := (array_elm_output_nat A B ) (at level 58).  
Notation "A :an= B" := (array_elm_assign_nat A B) (at level 58).
Notation "A :ab= B" := (array_elm_assign_bool A B) (at level 58).
Notation "A :as= B" := (array_elm_assign_string A B) (at level 58).
Notation "F {{{ A }}}" :=  (functionCall F A)(at level 88).
Notation "'printf(' S )" := (scrie S) (at level 92).
Notation "'scanf(' V )" := (citeste V) (at level 92).

Check pointer_decl_nat "a" nullptr. 
Check pointer_decl_nat "a" ("b" **). 
Check pointer_decl_nat "d" (&& "b"). 
Check "x" [['1']] :an= 2.
Check "x" [[10]].
Check dStg "st" ::= "plp".
Check dStg "sstg" ::=  "ana".
Check "st" :stg= "proiect".
Check dNat "a" ::= 9.
Check ifthen (3<'2) ("a" :nat= 3).
Check 1+'2.
Check "func" {{{["a";"b";"g"]}}}.
Check "v" [[10]] :lnat= [1;2;3].
Check switch (1+'2) [ defaultcase ("a" :nat= 5)].
Check switch (avar "a")
    [case (5) ("a" :nat= 4);
    case (3) ("a" :nat= 5);
     defaultcase ("a" :nat= 0)].
Check printf( "ceva" ).
Check scanf( "var" ).

(* A general type which includes all kind of types *)
Inductive ValuesType :=
  | err_undecl : ValuesType
  | err_assign : ValuesType
  | default : ValuesType
  | res_nat : ErrorNat -> ValuesType
  | res_bool : ErrorBool -> ValuesType
  | res_string : ErrorString -> ValuesType
  | res_pointer : Pointer -> ValuesType
  | res_array : ArrayExp -> ValuesType 
  | codebody : Stmt -> ValuesType.

Coercion codebody : Stmt >-> ValuesType.

(*Scheme Equality for Result.*)

(*Inductive type for functions *)

Inductive Body :=
| secv : Body -> Body -> Body (*Secventa de funcii si/sau declaratii de variabile *)
| default_nat_decl : string -> Body (*declarare nat cu valoare default*)
| default_bool_decl : string -> Body (*declarare int cu valoare default*)
| default_string_decl : string -> Body (*declarare string cu valoare default*)
| default_array_decl : string -> Body
| main : Stmt -> Body (* int main ()*)
| function : string -> list string -> Stmt -> Body. (* apel functii in maine () *)


Notation "'dec_global_nat' X" := (default_nat_decl X) (at level 90).
Notation "'dec_global_bool' X" := (default_bool_decl  X) (at level 90).
Notation "'dec_global_str' X" := (default_string_decl X) (at level 90).
Notation "'dec_global_arr' X" := (default_array_decl X) (at level 90).
Notation "S1 ;;' S2" := (secv S1 S2) (at level 93, right associativity).
Notation "'int' 'main()' { S }" := (main S)(at level 90).  
Notation "'void' F (){ S }" := (function F nil S)(at level 90).
Notation "'void' F (( p_1 , .. , p_n )){ S }" := (function F (cons p_1 .. (cons p_n nil) .. ) S)(at level 90).
 
Check
dec_global_nat "glob" ;;'
dec_global_str "str";;'

void "func_calcul" (("aux")){

   dNat "j" ::= 10 ;;
   pointer_decl_nat "d" (&& "aux");;
   dNat "sum" ::= 0 ;;
   while ("j" >' 0) do
       {  "sum" :nat= "d" *' 10 ;;
         "j" :nat= "j" -' 1

       }
};;'
 void "scrie" (("string")){
     printf( "string" )
  } ;;'
 
int main() {  

 dNat "a" ::= 9 ;; 
 dStg "st" ::= "plp";;

   ifthen (3<'2) 
    ( 
       "a" :nat= 3 ;;
       switch (avar "a")
       [       
        case (5) ("a" :nat= 4);
        case (3) ("a" :nat= 5);
        defaultcase ("a" :nat= 0) 
       ]
    ) ;;

  "x"[[10]] ;;
  "v" [[10]] :lnat= [1;2;3] ;;
    dNat "sum" ::= 0;;
   pointer_decl_nat "prt" (&& "sum");;
   "fun_calcul" {{{["ptr"]}}};;

   fors ( dNat "i" ::= 0 ~ "i" <' 6 ~ "i" :nat= "i" +' 1 ) 
   {
      printf("Contor");;
      "sum" :nat= "sum" +' "i" ;;  
      "x" [['1']] :as= "sum" 
    } 
 
}.


(* This function is useful when we need to update the environment based on the state of a variable *)
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
    | res_nat n1 => match t2 with
                   | res_nat n2 => true
                   | _ => false 
                     end
    | res_bool b1 => match t2 with
                   | res_bool b2 => true
                   | _ => false
                    end 
    | res_string b1 => match t2 with
                   | res_string b2 => true
                   | _ => false
                    end 
    | res_pointer b1 => match t2 with
                   | res_pointer b2 => true
                   | _ => false
                    end 
    | res_array b1 => match t2 with
                   | res_array b2 => true
                   | _ => false
                    end
    | default => match t2 with 
                     | default => true 
                     | _ => false 
                     end
    | codebody c1 => match t2 with 
                     | codebody c2 => true 
                     | _ => false 
                     end
    
  (* Fill in the implementation for the rest of the cases... *)
  end.

Compute (check_eq_over_types (res_nat 1000) (res_nat 100)). (* true *)
Compute (check_eq_over_types err_undecl (res_nat 100)). (* false *)
Compute (check_eq_over_types err_undecl (codebody ("x" :nat= 4))). (* false *)

(*
Complex configuration: <Environment, Memory, Stack>
                       Environment: mapping from a variable/function name (string) to a memory zone (nat)
                       Memory: mapping from a memory zone (nat) to a value of a specific type (Result)
                       Stack: list of environments (useful when implementing functions for storing
                                                    the program's state)
*)

Inductive Memory :=
  | memory_default : Memory
  | offset : nat -> Memory. (* offset which indicates the current number of memory zones *)

Scheme Equality for Memory.

(* Environment *)
Definition Env := string -> Memory.

(* Memory Layer *)
Definition MemLayer := Memory -> ValuesType.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack -> Config.

(* Function for updating the environment *)
Definition update_env (env: Env) (x: string) (n: Memory) : Env :=
  fun y =>
      if (andb (string_beq x y ) (Memory_beq (env y) memory_default))
      then
        n
      else
        (env y).

Definition env : Env := fun x => memory_default.

(* Initially each variable is assigned to a default memory zone *)
Compute (env "z"). (* The variable is not yet declared *)

(* Example of updating the environment, based on a specific memory offset *)
Compute (update_env env "x" (offset 9)) "x".

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Memory) (v : ValuesType) : MemLayer :=
  fun y =>
           if(andb(Memory_beq y type)(Memory_beq (env x) type))
             then 
               if(andb(check_eq_over_types err_undecl (mem y))(negb (check_eq_over_types default v)))
                 then err_undecl
                 else
                   if(andb(check_eq_over_types err_undecl (mem y))(check_eq_over_types default v))
                     then default
                     else
                       if(orb(check_eq_over_types default (mem y))(check_eq_over_types v (mem y)))
                         then v
                         else err_assign
           else (mem y).  


(* fiecare variabila/functie initiala este mapata nitial ca undeclared *)
Definition mem : MemLayer := fun x => err_undecl.

Definition memoryLeb (m1 : Memory) (m2 : Memory) : bool :=
match m1 with
| offset a => match m2 with
                      | offset b => if(Nat.leb a b) then true else false
                      | _ => false
                     end
| _ => false
end.

Definition update_config (conf1 : Config) (x : string) (v : ValuesType) : Config :=
match conf1 with
 | config contor env mem stack => if( memoryLeb ( update_env env x (offset (contor +1)) x) (offset contor ))
                                 then config contor (update_env env x (offset contor)) (update_mem mem (update_env env x ( offset contor )) x (offset contor) v) stack
                                 
                                 else config contor (update_env env x (offset (contor + 1))) (update_mem mem (update_env env x (offset (contor+1))) x (offset (contor + 1)) v) stack
end.

Definition GetMemoryLocation (conf : Config )(x : string ) : Memory :=
match conf with
| config contor env mem stack => (env x)
end.

Definition GetValue (conf : Config) (x : string) : ValuesType :=
match conf with
| config contor env mem stack => mem (env x)
end.


