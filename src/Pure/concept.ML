(*  Title:      Pure/concept.ML

Concepts as Pure sees them: the table from the predicate constant of each concept to the
concept, and the hook that rewrites a theorem after its concept premises are instantiated.
Loaded before ML_Antiquotations: no antiquotations.
*)

signature CONCEPT =
sig
  val add_predicate: string (*predicate constant*) -> string (*concept*) -> theory -> theory
  val concept_of_predicate: theory -> string -> string option
  val concept_of_prop: Proof.context -> term -> string option
  val is_concept_prop: Proof.context -> term -> bool
  structure Instantiation_Rewrite: HOOKS where type arg = Proof.context and type state = thm
  val rewrite_instantiated: Proof.context -> thm -> thm
end;

structure Concept: CONCEPT =
struct

(* the concept table *)

structure Data = Theory_Data
(
  type T = string Symtab.table;  (*predicate constant ~> concept*)
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun add_predicate c concept = Data.map (Symtab.update (c, concept));

val concept_of_predicate = Symtab.lookup o Data.get;

(*the concept whose predicate heads the HHF conclusion of t, judgment dropped*)
fun concept_of_prop ctxt t =
  (case Term.head_of (Object_Logic.drop_judgment ctxt (Logic.strip_assums_concl t)) of
    Const (c, _) => concept_of_predicate (Proof_Context.theory_of ctxt) c
  | _ => NONE);

val is_concept_prop = is_some oo concept_of_prop;


(* rewriting after instantiation *)

(*identity without hooks; session Concept rewrites selectors applied to instances*)
structure Instantiation_Rewrite = Hooks(type arg = Proof.context type state = thm);

fun rewrite_instantiated ctxt = Instantiation_Rewrite.invoke (Context.Proof ctxt) ctxt;

end;
