(*  Title:      Pure/simp_steps.ML
    Author:     Qiyuan Xu

A bound on the number of simplifier steps.

A step is a change of the term that the simplifier has made: a rule instance
applied, given or made by a simproc, a conditional one once its conditions are
proved (Raw_Simplifier.rewritec); or a congruence rule or procedure applied
that changed the term (congc).  An attempt that changes nothing is no step,
and neither is a beta step, which always ends.  So a bound ends every
simplification that keeps changing the term, but not work that changes
nothing: conditional rules whose conditions fail, again and again down to
simp_depth_limit; simprocs that fail; a looper that keeps making subgoals on
which nothing is changed, which nothing ends, as without the bound.

A bounded run "limited N f ctxt" gives f a context with a new step counter in
front of the open counters of ctxt.  The simplifier counts each step on every
open counter of its context.  A step is refused by EXCEEDED when one of them
has counted its bound; the refused step is still counted once, so that this
counter has reached its bound (bound + 1), and it refuses every later step
while it is open.  Without an open counter nothing is counted.
*)

signature SIMP_STEPS =
sig
  exception EXCEEDED
  val limited: int -> (Proof.context -> 'a) -> Proof.context -> 'a option
  val step: Proof.context -> unit
  val charge: int -> Proof.context -> unit
  val count: Proof.context -> int option
  val inherit: Proof.context -> Proof.context -> Proof.context
end;

structure Simp_Steps: SIMP_STEPS =
struct

exception EXCEEDED;


(* step counters *)

(*steps < 0: closed; steps = bound + 1: has reached its bound*)
type counter = {bound: int, steps: int Unsynchronized.ref};

fun is_open ({steps, ...}: counter) = ! steps >= 0;
fun has_reached_bound ({bound, steps}: counter) = ! steps > bound;

(*the counters of the enclosing bounded runs, innermost first*)
structure Data = Proof_Data
(
  type T = counter list;
  fun init _ = [];
);

val open_counters = filter is_open o Data.get;


(* counting *)

(*k steps, up to the first refused one, which counts unless a counter has
  already reached its bound; all open counters change by the same amount*)
fun charge k ctxt =
  (case open_counters ctxt of
    [] => ()
  | counters =>
      let
        (*the steps before the refused one; negative: a counter has reached
          its bound*)
        val room =
          fold (fn {bound, steps} => Integer.min (bound - ! steps)) counters k;
        fun add n =
          List.app (fn {steps, ...}: counter => steps := ! steps + n) counters;
      in
        if room < 0 then raise EXCEEDED
        else if room >= k then add k
        else (add (room + 1); raise EXCEEDED)
      end);

val step = charge 1;

(*the innermost open counter*)
fun count ctxt =
  (case open_counters ctxt of
    {steps, ...} :: _ => SOME (! steps)
  | [] => NONE);

fun inherit from = Data.put (open_counters from);


(* bounded runs *)

(*The result depends on the counters only: EXCEEDED if an enclosing counter
  has reached its bound, NONE if only the new one has, otherwise the result
  of f.  Interrupts pass.*)
fun limited bound f ctxt =
  let
    (*open only while f runs*)
    val steps = Unsynchronized.ref ~1;
    val ctxt' =
      Data.put ({bound = bound, steps = steps} :: open_counters ctxt) ctxt;
    val (result, n) =
      Unsynchronized.setmp steps 0
        (fn () => let val result = Exn.result f ctxt' in (result, ! steps) end)
        ();
  in
    if exists has_reached_bound (open_counters ctxt) then raise EXCEEDED
    else if n > bound then NONE
    else SOME (Exn.release result)
  end;

end;
