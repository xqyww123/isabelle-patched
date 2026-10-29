(*  Title:      Pure/setclass.ML

K, the setclass count of a theorem, recorded in the "setKls" tag (no tag when K = 0).  The
leading K premises are the first K premises that are not top-level SORT_CONSTRAINT premises; K
never counts a SORT_CONSTRAINT premise.  K is written where the light locale's own assumption is
pasted on, when a theorem is exported out of the locale (Locale.init): the leading K premises are
then the setclass premises -- premises headed by a light locale predicate -- pasted there; the
steps that keep K afterwards keep these positions, not necessarily their content
(LF.foo[unfolded LF_def] keeps K 1).  A hand-written [setclass n] sets K to n.

On the copying paths every step either writes K itself -- keep_count, keeping_count and
shift_count, under preconditions that count no SORT_CONSTRAINT premise, and Rule_Cases.save,
which copies its input's K back -- or goes through restore_count: Assumption.thm_export after
each layer, Morphism.morphism around each fact function; simplification and the kernel's
inference rules clear K.  An equation that rewrites an implication (an [unfolded]/[folded]
argument, a rewrites mixin, a declared rulify rule) can break keep_count's precondition; the user
then writes K with [setclass n].  Two known limitations, reachable only from custom ML, leave K
wrong: a custom export layer that keeps its input's tag and pastes premises in front, and an
export morphism whose custom layers first remove a premise and then paste one in front
(restore_counts compares only the morphism's input and output).

put checks only k <= nprems: this file is loaded before Drule, which recognises SORT_CONSTRAINT.
The readers of the leading K premises (more_setclass.ML) are defined on every theorem put
accepts.
*)

signature SETCLASS =
sig
  val setclass_tagN: string
  val lookup_nat_tag: string -> thm -> int option
  val count_of: thm -> int
  val put: int -> thm -> thm
  val with_count: (int -> thm -> thm -> int) -> thm -> thm -> thm
  val keep_count: thm -> thm -> thm
  val keeping_count: (thm -> thm) -> thm -> thm
end;

structure Setclass: SETCLASS =
struct

(* tags *)

fun lookup_nat_tag tagN th =
  (case AList.lookup (op =) (Thm.get_tags th) tagN of
    NONE => NONE
  | SOME s =>
      (case Lexicon.read_nat s of
        SOME n => SOME n
      | _ => raise THM ("Malformed '" ^ tagN ^ "' tag of theorem", 0, [th])));

val setclass_tagN = "setKls";

val count_of = the_default 0 o lookup_nat_tag setclass_tagN;

(*K = 0 removes every entry; otherwise the value changes in place, since
  Thm.eq_thm_strict compares tags in order*)
fun set 0 = Thm.untag_rule setclass_tagN
  | set k = Thm.map_tags (Properties.put (setclass_tagN, string_of_int k));

(*put k th: K becomes k when 0 < k <= nprems th, otherwise the tag is removed ("unknown");
  th itself when it already carries that value*)
fun put k th =
  let val k' = if 0 < k andalso k <= Thm.nprems_of th then k else 0
  in if count_of th = k' then th else set k' th end;

(*an untagged th gives th' itself; otherwise th' gets the rule's K through put*)
fun with_count rule th th' =
  (case count_of th of
    0 => th'
  | k => put (rule k th th') th');

(*th' derived from th by a step that adds, removes or reorders no premise in front of or among
  the leading K, SORT_CONSTRAINT premises aside; it may change their content (instantiation,
  rewriting) and add premises only behind them (a conclusion split off at the end)*)
val keep_count = with_count (fn k => fn _ => fn _ => k);

(*f th with th's K, for an f that meets keep_count's precondition.  Wrapping the function
  value keeps whatever f staged before it saw th (a simpset built once per partial application);
  where stock is a fun clause over a named theorem, or the result comes out of a case branch,
  keep_count is appended instead.*)
fun keeping_count f th = keep_count th (f th);

end;
