(*  Title:      Pure/hooks.ML

Generic hooks stored in context data, after phi-system's
Phi_Logic_Programming_Reasoner/library/tools/Hook.ML.

A hook is a function arg -> state -> state.  Hooks are keyed by
(priority, long name of the owning theory) and run in ascending order of
priority, threading the state.  Within one theory two hooks may not share a
priority.
*)

signature HOOK_ARG =
sig
  type arg
  type state
end;

signature HOOKS =
sig
  type arg
  type state
  type priority = int  (*smaller runs earlier*)
  val add: priority -> (arg -> state -> state) -> Context.generic -> Context.generic
  val add': priority * theory (*owner*) -> (arg -> state -> state) ->
    Context.generic -> Context.generic
  val remove: priority * string (*long name of the owner*) -> Context.generic -> Context.generic
  val remove': priority * theory (*owner*) -> Context.generic -> Context.generic
  val invoke: Context.generic -> arg -> state -> state
  val clean: Context.generic -> Context.generic
  val is_empty: Context.generic -> bool
  exception Success of state  (*stop; the result is this state*)
  exception ReEntry of arg * state  (*restart all hooks on this arg and state*)
  exception Return of state  (*this hook's result; continue with the next hook*)
  val invoke_until_success: Context.generic -> (arg -> state -> state) (*fallback*) ->
    arg -> state -> state
end;

functor Hooks(Arg: HOOK_ARG): HOOKS =
struct

type arg = Arg.arg;
type state = Arg.state;
type priority = int;

structure Tab = Table(type key = priority * string val ord = prod_ord int_ord fast_string_ord);

structure Data = Generic_Data
(
  type T = (arg -> state -> state) Tab.table;
  val empty = Tab.empty;
  val merge = Tab.merge (K true);
);

fun add' (priority, thy) f = Data.map (Tab.update_new ((priority, Context.theory_long_name thy), f));
fun add priority f context = add' (priority, Context.theory_of context) f context;

fun remove key = Data.map (Tab.delete_safe key);
fun remove' (priority, thy) = remove (priority, Context.theory_long_name thy);

val clean = Data.map (K Tab.empty);
val is_empty = Tab.is_empty o Data.get;

exception Success of state;
exception ReEntry of arg * state;
exception Return of state;

(*Return ends one hook, ReEntry restarts all of them; the arg of the last restart and the final
  state*)
fun run hooks arg st =
  (arg, Tab.fold (fn (_, f) => fn st => f arg st handle Return st' => st') hooks st)
  handle ReEntry (arg', st') => run hooks arg' st';

(*Success ends the run; otherwise the fallback gets the arg of the last restart*)
fun invoke_until_success context fallback arg st =
  uncurry fallback (run (Data.get context) arg st) handle Success st' => st';

fun invoke context = invoke_until_success context (K I);

end;
