(*  Title:      Pure/more_setclass.ML

Operations on K that need Drule (head of setclass.ML): premise counts that skip SORT_CONSTRAINT,
the positions of the leading K premises, and the "consumes" primitives of Rule_Cases, which live
here so that get_consumes can default to the leading K premises.
*)

signature SETCLASS =
sig
  include SETCLASS
  val shift_count: thm -> thm -> thm
  val restore_count: thm -> thm -> thm
  val restore_counts: thm list -> thm list -> thm list
  val leading_span: thm -> int
  val leading_prems: thm -> term list
  val lookup_consumes: thm -> int option
  val get_consumes: thm -> int
  val put_consumes: int option -> thm -> thm
  val own_prems: thm -> term list
  val own_major_prem: thm -> term
  val strong_consumes: thm -> int
  val put_major_prem_first: thm -> thm
  val fill_leading: int -> thm list -> thm -> int * thm list
  val discharge: thm list -> thm -> thm
end;

structure Setclass: SETCLASS =
struct

open Setclass;


(* steps that move K *)

fun count_prems th = length (filter_out Drule.is_sort_constraint (Thm.prems_of th));

(*th' derived from th by a step whose every added or removed premise lies in front,
  SORT_CONSTRAINT premises aside: more premises are ordinary ones pasted in front, K becomes 0;
  fewer move K by the difference*)
val shift_count = with_count (fn k => fn th => fn th' =>
  let val d = count_prems th' - count_prems th in if d > 0 then 0 else k + d end);

(*th' made from th by one step: th' as it is when it carries K; otherwise th's K moved by
  shift_count*)
fun restore_count th th' = if count_of th' > 0 then th' else shift_count th th';

(*wrapped around each fact function of a morphism: one output per input, in input order; when
  the lengths differ nothing is done (Eisbach's match changes the length)*)
fun restore_counts ths ths' =
  if length ths <> length ths' orelse forall (fn th => count_of th = 0) ths then ths'
  else map2 restore_count ths ths';


(* the leading K premises *)

(*their positions, from 1*)
fun leading_positions th =
  let
    fun positions _ 0 _ = []
      | positions _ _ [] = []
      | positions i k (prem :: prems) =
          if Drule.is_sort_constraint prem then positions (i + 1) k prems
          else i :: positions (i + 1) (k - 1) prems;
  in positions 1 (count_of th) (Thm.prems_of th) end;

(*the number of premises up to the last of them; all premises when fewer than K are not
  SORT_CONSTRAINT*)
fun leading_span th =
  let val ps = leading_positions th in
    if length ps < count_of th then Thm.nprems_of th
    else if null ps then 0
    else List.last ps
  end;

fun leading_prems th = map (nth (Thm.prems_of th) o Integer.add ~1) (leading_positions th);


(* consumes *)

val consumes_tagN = "consumes";

val lookup_consumes = lookup_nat_tag consumes_tagN;

(*a rule consumes at least its leading K premises*)
fun get_consumes th = Integer.max (leading_span th) (the_default 0 (lookup_consumes th));

fun put_consumes NONE th = th
  | put_consumes (SOME n) th = th
      |> Thm.untag_rule consumes_tagN
      |> Thm.tag_rule (consumes_tagN, string_of_int (if n < 0 then Thm.nprems_of th + n else n));


(* the rule's own premises: after the leading K *)

fun own_prems th = drop (leading_span th) (Thm.prems_of th);

fun own_major_prem th =
  (case own_prems th of
    prem :: _ => Logic.strip_assums_concl prem
  | [] => Thm.major_prem_of th);

fun strong_consumes th = get_consumes th - leading_span th;

(*rotate the first own premise in front of the leading K; with nothing to rotate the rule is
  returned as it is, since rearrange_prems clears the tags*)
fun put_major_prem_first th =
  let val span = leading_span th and n = Thm.nprems_of th in
    if span = 0 orelse n = span then th else Drule.rearrange_prems [span] th
  end;


(* facts into the leading K premises *)

(*the facts for Drule.multi_resolve on th's positions 1 .. n, and how many of them are used:
  each position takes the next fact, except a SORT_CONSTRAINT premise up to the last of the
  leading K premises, which gets Drule.asm_rl and stays; stops when the facts or the positions
  run out*)
fun fill_leading n facts th =
  let
    val span = leading_span th;
    val prems = Thm.prems_of th;
    fun skipped i = i <= span andalso Drule.is_sort_constraint (nth prems (i - 1));
    fun fill _ [] = (0, [])
      | fill i (facts as fact :: rest) =
          if i > n then (0, [])
          else if skipped i then fill (i + 1) facts ||> cons Drule.asm_rl
          else fill (i + 1) rest |>> Integer.add 1 ||> cons fact;
  in fill 1 facts end;

fun discharge facts th =
  (case count_of th of
    0 => th
  | k =>
      let val (m, facts') = fill_leading (leading_span th) facts th in
        if m < k then raise THM ("discharge: too few facts", k, th :: facts)
        else facts' MRS th
      end);

end;
