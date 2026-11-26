(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Martin Desharnais, LMU Muenchen

Isabelle tactics as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_TACTIC =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover
  type base_slice = Sledgehammer_ATP_Systems.base_slice

  val is_tactic_prover : string -> bool
  val good_slices_of_tactic_prover : string -> base_slice list
  val run_tactic_prover : mode -> string -> prover
end;

structure Sledgehammer_Prover_Tactic : SLEDGEHAMMER_PROVER_TACTIC =
struct

open ATP_Problem_Generate
open ATP_Proof
open Sledgehammer_Proof_Methods
open Sledgehammer_Prover

val is_tactic_prover : string -> bool = is_some o Try0.get_proof_method

local

val slices_of_max_facts = map (fn max_facts => (1, false, false, max_facts, "mesh"))

in

(* FUDGE *)
fun good_slices_of_tactic_prover "metis" = slices_of_max_facts [0, 64, 32, 8, 16, 4, 2, 1]
  | good_slices_of_tactic_prover "fastforce" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover "simp" = slices_of_max_facts [0, 16, 32, 8, 64, 4, 1, 2]
  | good_slices_of_tactic_prover "auto" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover _ = slices_of_max_facts [0, 2, 8, 16, 32, 64]

end

(*the proof method that stands for a Try0 method, if there is one*)
fun meth_of "algebra" = SOME Algebra_Method
  | meth_of "argo" = SOME Argo_Method
  | meth_of "auto" = SOME Auto_Method
  | meth_of "blast" = SOME Blast_Method
  | meth_of "fastforce" = SOME Fastforce_Method
  | meth_of "force" = SOME Force_Method
  | meth_of "linarith" = SOME Linarith_Method
  | meth_of "meson" = SOME Meson_Method
  | meth_of "metis" = SOME (Metis_Method (NONE, NONE, []))
  | meth_of "order" = SOME Order_Method
  | meth_of "presburger" = SOME Presburger_Method
  | meth_of "satx" = SOME SATx_Method
  | meth_of "simp" = SOME Simp_Method
  | meth_of _ = NONE

fun run_tactic_prover mode name ({slices, timeout, ...} : params)
    ({state, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) slice =
  let
    val (basic_slice as (slice_size, _, _, _, _), No_Slice) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val non_chained = filter_out is_fact_chained facts
    val ctxt = Proof.context_of state

    fun run_try0 () : string option =
      let
        val run_timeout = slice_timeout slice_size slices timeout
        val (locals, globals) = List.partition (fn ((_, (sc, _)), _) => sc <> Global) non_chained
        fun is_cartouche str = String.isPrefix "\<open>" str andalso String.isSuffix "\<close>" str
        fun xref_of_fact (((name, _), thm) : Sledgehammer_Fact.fact) : Try0.xref =
          if is_cartouche name then
            (Facts.Fact (Pretty.pure_string_of (Thm.pretty_thm ctxt thm)), [])
          else
            Sledgehammer_Util.xref_of_name ctxt name
        val usings_xrefs = map xref_of_fact (sort_by (fst o fst) locals)
        val direct_xrefs = map xref_of_fact (sort_by (fst o fst) globals)
        val facts : Try0.facts = {usings = usings_xrefs, directs = direct_xrefs, simps = [],
          intros = [], elims = [], dests = []}
        (*Try0 works on the first subgoal*)
        val (state', prefix) =
          if subgoal = 1 then (state, "")
          else (Proof.prefer subgoal state, "prefer " ^ string_of_int subgoal ^ " ")
      in
        Try0.get_proof_method_or_noop name (SOME run_timeout) facts state'
        |> Option.map (fn {command, ...} => prefix ^ command)
      end

    val timer = Timer.startRealTimer ()
    val (outcome, command) =
      (case run_try0 () of
        NONE => (SOME GaveUp, "")
      | SOME command => (NONE, command))
      handle ERROR _ => (SOME GaveUp, "")
           | Timeout.TIMEOUT _ => (SOME TimedOut, "")
    val run_time = Timer.checkRealTimer timer

    val used_facts =
      (case outcome of
        NONE => (found_something name; map fst non_chained)
      | SOME _ => [])

    val meth = meth_of name

    (*a preplay result replaces Try0's command only if it played the proof method that stands for
      the Try0 method*)
    val message = fn preplay_outcome =>
      (case outcome of
        NONE =>
        let
          val banner = proof_banner mode name
        in
          (case (meth, preplay_outcome) of
            (SOME _, SOME (preplay_result as (_, (_, Played _)))) =>
              one_line_proof_text (preplay_result, banner, subgoal, subgoal_count)
          | _ => try_command_line banner (Played run_time) command)
        end
      | SOME failure => string_of_atp_failure failure)
  in
    {outcome = outcome, used_facts = used_facts, used_from = facts,
     preferred_methss = (the_default (Metis_Method (NONE, NONE, [])) meth, []),
     run_time = run_time, message = message}
  end

end;
