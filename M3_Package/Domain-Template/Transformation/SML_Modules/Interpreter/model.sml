(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store );
val counter      = 0;

exception runtime_error;

fun error msg = ( print msg; raise runtime_error );

fun typeToString BOOL   = "bool"
  | typeToString INT    = "integer"
  | typeToString ERROR  = "error";

fun envEntryToString(id, t, loc) = "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")";

fun showEnv [] = print "\n"
  | showEnv (entry::env) = (
                            print("\n" ^ envEntryToString entry);
                            showEnv env
                           );

fun accessEnv(id1, (env, counter, s) ) = 
	let
		val msg = "Error: accessEnv" ^id1^ " not found.";

		fun aux [] = error msg
                  | aux ((id2, t, loc)::env) =
                        if id1 = id2 then (t, loc)
                        else aux env
        in
           aux env
        end;


fun updateStore(loc1, dv, (env,counter,s) ) = 
    let
        val msg = "Error: updateStore " ^ loc1 ^ " not found.";
        val x = counter
        val store = s
        fun aux (_,_,_,[])                  = error msg
          | aux (loc, dv, x, s::ss) = if loc = x then (env, counter, dv::ss)
                                      else (env,counter, s::aux(loc, dv, x-1, ss))
    in
        aux (loc1, dv, x, store)
    end;


fun new(env,counter,store) = (env, counter + 1, store);

fun updateEnv(id, t, loc, (env, counter, store)) = ((id, t, loc)::env, counter, store);

fun getLoc((t, loc)) = loc;

fun getType((t, loc)) = t;

fun accessStore(loc1, (env, counter, s))  = 
    let 
        val msg = "Error: accessStore " ^ loc1 ^ " not found.";
        val x = counter
        fun aux (_,_,[])              = error msg
          | aux (loc, x, s::ss) = if loc = x then s
                                  else aux(loc, x-1, ss)
    in
        aux(loc1, x, s)
    end;








(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)















