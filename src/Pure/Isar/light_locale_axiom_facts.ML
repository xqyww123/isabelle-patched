(*  Title:      Pure/Isar/light_locale_axiom_facts.ML

Unconditional facts "LF t" of light locale predicates, indexed by proposition; the
repair-phase tools on setclass premises, the premises headed by a light predicate (contracts in
plan decision 19), which skip and ignore top-level SORT_CONSTRAINT premises; the term part of an
export and the export of light targets that pastes nothing on (plan decision 9).
*)

signature LIGHT_LOCALE_AXIOM_FACTS =
sig
  val light_predicate_of: Proof.context -> term -> string option
  val is_light_prop: Proof.context -> term -> bool
  val add: thm -> Context.generic -> Context.generic
  val add_attribute: attribute
  val retrieve: Proof.context -> term -> thm list
  val count_setclass_prems: Proof.context -> thm -> int
  val discharge_setclass_prems: Proof.context -> thm -> thm
  val instance_tac: Proof.context -> int -> tactic
  val close_setclass_prems_tac: Proof.context -> int -> int -> tactic
  val resolve_closing_setclass_prems: Proof.context -> thm list -> int -> tactic
  val discharge_morphism: Proof.context -> morphism
  val unchanged_by: morphism -> thm -> bool
  val replace_fact: string -> (thm -> thm) -> morphism -> morphism
  val light_export: local_theory -> Proof.context -> thm -> thm
end;

structure Light_Locale_Axiom_Facts: LIGHT_LOCALE_AXIOM_FACTS =
struct

(* light predicates *)

(*the light predicate a proposition applies, by its head constant*)
fun light_predicate_of ctxt t =
  (case Term.head_of (Object_Logic.drop_judgment ctxt t) of
    Const (c, _) =>
      if Locale.is_light_predicate (Proof_Context.theory_of ctxt) c then SOME c else NONE
  | _ => NONE);

val is_light_prop = is_some oo light_predicate_of;


(* predicate facts *)

structure Data = Generic_Data
(
  type T = thm Item_Net.T;
  val empty = Thm.item_net;
  val merge = Item_Net.merge;
);

(*only unconditional facts of a light predicate are recorded, beta-eta normalised*)
fun add th context =
  let val th' = Conv.fconv_rule Drule.beta_eta_conversion th in
    if Thm.nprems_of th' = 0 andalso is_light_prop (Context.proof_of context) (Thm.concl_of th')
    then Data.map (Item_Net.update (Thm.trim_context th')) context
    else context
  end;

val add_attribute = Thm.declaration_attribute add;

fun retrieve ctxt t =
  map (Thm.transfer' ctxt) (Item_Net.retrieve (Data.get (Context.Proof ctxt)) t);


(* setclass premises *)

(*the leading ones, SORT_CONSTRAINT premises skipped; not bounded by K*)
fun count_setclass_prems ctxt th =
  Thm.prems_of th
  |> take_prefix (fn P => Drule.is_sort_constraint P orelse is_light_prop ctxt P)
  |> filter_out Drule.is_sort_constraint
  |> length;

(*the instantiation of a unifier, keyed by the variables' instantiated types; fresh variables
  are above maxidx*)
fun unifier_insts ctxt maxidx (t, u) =
  let
    val env = Pattern.unify (Context.Proof ctxt) (t, u) (Envir.empty maxidx);
    val tyenv = Envir.type_env env;
    val instT =
      TVars.build (tyenv |> Vartab.fold (fn (ai, (S, T)) =>
        TVars.add ((ai, S), Thm.ctyp_of ctxt (Envir.norm_type tyenv T))));
    val inst =
      Vars.build (Envir.term_env env |> Vartab.fold (fn (xi, (T, _)) =>
        Vars.add ((xi, Envir.norm_type tyenv T),
          Thm.cterm_of ctxt (Envir.norm_term env (Var (xi, T))))));
  in SOME (instT, inst) end
  handle Pattern.Unif => NONE | Pattern.Pattern => NONE;

(*rule R: the first premise of th discharged by the fact F, whose variables are renamed apart;
  Pattern.match of F against the premise, else Pattern.unify with F on the left; the instantiation
  may bind no variable of th outside that premise, SORT_CONSTRAINT premises ignored*)
fun discharge_prem_by ctxt th =
  let
    val (P, rest) = Thm.dest_implies (Thm.cprop_of th);
    val ts =
      filter_out Drule.is_sort_constraint (Logic.strip_imp_prems (Thm.term_of rest)) @
      Logic.strip_imp_concl (Thm.term_of rest) :: Thm.terms_of_tpairs (Thm.tpairs_of th);
    (*F's renamed variables and those unification creates are above maxidx th, never in th*)
    val tvars = fold Term.add_tvar_names ts [];
    val vars = fold Term.add_var_names ts [];
    fun allowed (instT, inst) =
      not (TVars.exists (fn ((ai, _), _) => member (op =) tvars ai) instT) andalso
      not (Vars.exists (fn ((xi, _), _) => member (op =) vars xi) inst);
    fun discharge F insts =
      let
        val th1 = Thm.instantiate_beta insts th;
        val F1 = Thm.instantiate_beta insts F;
      in
        if Thm.prop_of F1 aconv Thm.prem_of th1 1 then Thm.implies_elim th1 F1
        else
          Thm.implies_elim (Conv.gconv_rule Drule.beta_eta_conversion 1 th1)
            (Conv.fconv_rule Drule.beta_eta_conversion F1)
      end;
  in
    fn fact =>
      let val F = Drule.incr_indexes th fact in
        (SOME (Thm.match (Thm.cprop_of F, P))
          handle Pattern.MATCH =>
            unifier_insts ctxt (Int.max (Thm.maxidx_of th, Thm.maxidx_of F))
              (Thm.prop_of F, Thm.term_of P))
        |> Option.mapPartial (fn insts => if allowed insts then SOME (discharge F insts) else NONE)
      end
  end;

(*the first premise that is not SORT_CONSTRAINT, when it is a setclass premise: rotated to the
  front, the others keeping their order, and discharged*)
fun discharge_first_prem ctxt th =
  let
    val prems = Thm.prems_of th;
    val j = find_index (not o Drule.is_sort_constraint) prems;
  in
    if j < 0 orelse not (is_light_prop ctxt (nth prems j)) then NONE
    else
      let
        val th' = if j = 0 then th else Drule.rearrange_prems [j] th;
      in get_first (discharge_prem_by ctxt th') (retrieve ctxt (nth prems j)) end
  end;

(*stops at the first premise it cannot discharge; th itself when none is discharged*)
fun discharge_setclass_prems ctxt th =
  Setclass.shift_count th (perhaps (perhaps_loop (discharge_first_prem ctxt)) th);

fun instance_tac ctxt = SUBGOAL (fn (goal, i) =>
  let val C = Logic.strip_assums_concl goal in
    if is_light_prop ctxt C then SOLVED' (resolve_tac ctxt (retrieve ctxt C)) i else no_tac
  end);

(*instance_tac on the first subgoal from i on that is not a SORT_CONSTRAINT*)
fun next_instance_tac ctxt i st =
  (case find_index (not o Drule.is_sort_constraint o Logic.strip_assums_concl)
      (drop (i - 1) (Thm.prems_of st)) of
    ~1 => no_tac st
  | d => instance_tac ctxt (i + d) st);

(*no DETERM, no REPEAT*)
fun close_setclass_prems_tac ctxt n i = EVERY (replicate n (next_instance_tac ctxt i));

(*the rules' results in list order, each rule's leading setclass subgoals closed*)
fun resolve_closing_setclass_prems ctxt rules =
  fold_rev (fn r => fn tac =>
      (fn i =>
        resolve_tac ctxt [r] i THEN close_setclass_prems_tac ctxt (count_setclass_prems ctxt r) i)
      APPEND' tac)
    rules (K no_tac);

(*rule R is the identity on an empty table*)
fun discharge_morphism ctxt =
  if Item_Net.is_empty (Data.get (Context.Proof ctxt)) then Morphism.identity
  else Morphism.thm_morphism "Light_Locale_Axiom_Facts.discharge" (discharge_setclass_prems ctxt);


(* the term part of an export *)

(*the term part of phi; the theorem part of an export morphism would also prepend the layer's
  assumptions*)
fun unchanged_by phi th =
  null (Thm.hyps_of th) andalso
    (case try (Morphism.term phi) (Thm.full_prop_of th) of
      SOME p => p aconv Thm.full_prop_of th
    | NONE => false);

(*phi with its theorem part replaced*)
fun replace_fact name thm phi =
  Morphism.morphism name
   {binding = [K (Morphism.binding phi)],
    typ = [K (Morphism.typ phi)],
    term = [K (Morphism.term phi)],
    fact = [K (map thm)]};


(* the export that pastes nothing on *)

(*unfold the fixed variables defined between lthy and ctxt, generalise the ones ctxt does not
  know, add no assumption; K is copied back by Rule_Cases.save and stays right, since only
  top-level SORT_CONSTRAINT premises can go, which K does not count; the rule-case tags too, for
  th without such a premise; other tags are not copied back*)
fun light_export lthy ctxt th =
  let
    val defined =
      Frees.build (Thm.fold_terms {hyps = false} Frees.add_frees th) |> Frees.list_set
      |> map_filter (fn v =>
        let val t = Assumption.export_term lthy ctxt (Free v)
        in if t aconv Free v then NONE else SOME (v, Thm.cterm_of lthy t) end);
  in
    th
    |> Thm.instantiate_frees (TFrees.empty, Frees.make defined)
    |> singleton (Variable.export lthy ctxt)
    |> Goal.norm_result ctxt
    |> Rule_Cases.save th
  end;

end;
