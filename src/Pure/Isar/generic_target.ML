(*  Title:      Pure/Isar/generic_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common target infrastructure.
*)

signature GENERIC_TARGET =
sig
  (*auxiliary*)
  val export_abbrev: Proof.context ->
      (term -> term) -> term -> term * ((string * sort) list * (term list * term list))
  val check_mixfix: Proof.context -> binding * (string * sort) list -> mixfix -> mixfix
  val check_mixfix_global: binding * bool -> mixfix -> mixfix

  (*background primitives*)
  val background_foundation: ((binding * typ) * mixfix) * (binding * term) ->
    term list * term list -> local_theory -> (term * thm) * local_theory
  val background_declaration: Morphism.declaration_entity -> local_theory -> local_theory
  val background_abbrev: binding * term -> term list -> local_theory -> (term * term) * local_theory
  val add_foundation_interpretation: (binding * (term * term list) -> Context.generic -> Context.generic) ->
    theory -> theory

  (*nested local theories primitives*)
  val standard_facts: local_theory -> Proof.context -> Attrib.fact list -> Attrib.fact list
  val standard_notes: (int * int -> bool) -> string -> Attrib.fact list ->
    local_theory -> local_theory
  val standard_declaration: (int * int -> bool) -> Morphism.declaration_entity ->
    local_theory -> local_theory
  val light_standard_declaration: (int * int -> bool) -> Morphism.declaration_entity ->
    local_theory -> local_theory
  val standard_const: (int * int -> bool) -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> local_theory
  val local_interpretation: Locale.registration ->
    local_theory -> local_theory

  (*lifting target primitives to local theory operations*)
  val define: (((binding * typ) * mixfix) * (binding * term) ->
      term list * term list -> local_theory -> (term * thm) * local_theory) ->
    bool -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val notes:
    (string -> Attrib.fact list -> Attrib.fact list -> local_theory -> local_theory) ->
    string -> Attrib.fact list -> local_theory -> (string * thm list) list * local_theory
  val light_notes: string -> string -> Attrib.fact list -> local_theory ->
    (string * thm list) list * local_theory
  val abbrev: (Syntax.mode -> binding * mixfix -> term ->
      term list * term list -> local_theory -> local_theory) ->
    Syntax.mode -> (binding * mixfix) * term -> local_theory -> (term * term) * local_theory

  (*theory target primitives*)
  val theory_target_foundation: ((binding * typ) * mixfix) * (binding * term) ->
     term list * term list -> local_theory -> (term * thm) * local_theory
  val theory_target_notes: string -> Attrib.fact list -> Attrib.fact list ->
    local_theory -> local_theory
  val theory_target_abbrev: Syntax.mode -> (binding * mixfix) -> term -> term list * term list ->
    local_theory -> local_theory

  (*theory target operations*)
  val theory_abbrev: Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> (term * term) * local_theory
  val theory_declaration: Morphism.declaration_entity -> local_theory -> local_theory
  val light_theory_declaration: Morphism.declaration_entity -> local_theory -> local_theory
  val theory_registration: Locale.registration -> local_theory -> local_theory

  (*locale target primitives*)
  val locale_target_notes: string -> string -> Attrib.fact list -> Attrib.fact list ->
    local_theory -> local_theory
  val locale_target_abbrev: string -> Syntax.mode ->
    (binding * mixfix) -> term -> term list * term list -> local_theory -> local_theory
  val locale_target_declaration: string -> {syntax: bool, pos: Position.T} ->
    Morphism.declaration_entity -> local_theory -> local_theory
  val locale_target_const: string -> (morphism -> bool) -> Syntax.mode ->
    (binding * mixfix) * term -> local_theory -> local_theory

  (*locale operations*)
  val locale_abbrev: string -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> (term * term) * local_theory
  val locale_declaration: string -> {syntax: bool, pervasive: bool, pos: Position.T} ->
    Morphism.declaration_entity -> local_theory -> local_theory
  val locale_const: string -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> local_theory
  val locale_dependency: string -> Locale.registration ->
    local_theory -> local_theory
  val gen_locale_dependency: (Locale.registration -> Context.generic -> Context.generic) ->
    string -> Locale.registration -> local_theory -> local_theory
end

structure Generic_Target: GENERIC_TARGET =
struct

(** consts **)

fun export_abbrev lthy preprocess rhs =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    val rhs' = rhs
      |> Assumption.export_term lthy (Local_Theory.target_of lthy)
      |> preprocess;
    val term_params =
      map Free (sort (Variable.fixed_ord lthy o apply2 #1) (Variable.add_fixed lthy rhs' []));
    val u = fold_rev lambda term_params rhs';
    val global_rhs = singleton (Variable.polymorphic thy_ctxt) u;

    val type_tfrees = TFrees.build (TFrees.add_tfreesT (Term.fastype_of u));
    val extra_tfrees =
      TFrees.build (TFrees.add_tfrees_unless (TFrees.defined type_tfrees) u)
      |> TFrees.keys;
    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
  in (global_rhs, (extra_tfrees, (type_params, term_params))) end;

fun check_mixfix ctxt (b, extra_tfrees) mx =
  if null extra_tfrees then mx
  else
   (if Context_Position.is_visible ctxt then
      warning
        ("Additional type variable(s) in specification of " ^ Binding.print b ^ ": " ^
          commas (map (Syntax.string_of_typ ctxt o TFree) extra_tfrees) ^
          (if Mixfix.is_empty mx then ""
           else "\nDropping mixfix syntax " ^ Pretty.string_of (Mixfix.pretty_mixfix mx)))
    else (); NoSyn);

fun check_mixfix_global (b, no_params) mx =
  if no_params orelse Mixfix.is_empty mx then mx
  else
    (warning ("Dropping global mixfix syntax: " ^ Binding.print b ^ " " ^
      Pretty.string_of (Mixfix.pretty_mixfix mx)); NoSyn);

fun same_const (Const (c, _), Const (c', _)) = c = c'
  | same_const (t $ _, t' $ _) = same_const (t, t')
  | same_const _ = false;

fun const_decl phi_pred prmode ((b, mx), rhs) = Morphism.entity (fn phi => fn context =>
  if phi_pred phi then
    let
      val b' = Morphism.binding phi b;
      val rhs' = Morphism.term phi rhs;
      val same_shape = Term.aconv_untyped (rhs, rhs');
      val same_stem = same_shape orelse same_const (rhs, rhs');
      val const_alias =
        if same_shape then
          (case rhs' of
            Const (c, T) =>
              let
                val thy = Context.theory_of context;
                val ctxt = Context.proof_of context;
              in
                (case Type_Infer_Context.const_type ctxt c of
                  SOME T' => if Sign.typ_equiv thy (T, T') then SOME c else NONE
                | NONE => NONE)
              end
          | _ => NONE)
        else NONE;
    in
      (case const_alias of
        SOME c =>
          context
          |> Context.mapping (Sign.const_alias b' c) (Proof_Context.const_alias b' c)
          |> Morphism.form_entity (Proof_Context.generic_notation true prmode [(rhs', mx)])
      | NONE =>
          context
          |> Proof_Context.generic_add_abbrev Print_Mode.internal
            (b', Term.close_schematic_term rhs')
          |-> (fn (const as Const (c, _), _) => same_stem ?
                (Proof_Context.generic_revert_abbrev (#1 prmode) c #>
                 same_shape ?
                  Morphism.form_entity (Proof_Context.generic_notation true prmode [(const, mx)]))))
    end
  else context);



(** background primitives **)

structure Foundation_Interpretations = Theory_Data
(
  type T = ((binding * (term * term list) -> Context.generic -> Context.generic) * stamp) list
  val empty = [];
  val merge = Library.merge (eq_snd (op =));
);

fun add_foundation_interpretation f =
  Foundation_Interpretations.map (cons (f, stamp ()));

fun foundation_interpretation binding_const_params lthy =
  let
    val interps = Foundation_Interpretations.get (Proof_Context.theory_of lthy);
    val interp = fold (fn (f, _) => f binding_const_params) interps;
  in
    lthy
    |> Local_Theory.background_theory (Context.theory_map interp)
    |> Local_Theory.map_contexts (K (Context.proof_map interp))
  end;

fun background_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val params = type_params @ term_params;
    val target_params = type_params
      @ take_prefix is_Free (Variable.export_terms lthy (Local_Theory.target_of lthy) term_params);
    val mx' = check_mixfix_global (b, null params) mx;

    val (const, lthy2) = lthy
      |> Local_Theory.background_theory_result (Sign.declare_const lthy ((b, U), mx'));
    val lhs = Term.list_comb (const, params);

    val ((_, def), lthy3) = lthy2
      |> Local_Theory.background_theory_result
        (Thm.add_def (Proof_Context.defs_context lthy2) false false
          (Thm.def_binding_optional b b_def, Logic.mk_equals (lhs, rhs)))
      ||> foundation_interpretation (b, (const, target_params));
  in ((lhs, def), lthy3) end;

(*morphism: the export morphism from the local theory to a layer's context*)
fun gen_background_declaration morphism decl lthy =
  let
    fun theory_decl context =
      let val thy_ctxt = Proof_Context.init_global (Context.theory_of context)
      in Morphism.form (Morphism.transform (morphism lthy thy_ctxt) decl) context end;
  in Local_Theory.background_theory (Context.theory_map theory_decl) lthy end;

val background_declaration = gen_background_declaration Local_Theory.standard_morphism;


(* light export morphisms *)

(*stored as it is iff hyps-free and noted or declared under the re-declaration flag
  (Local_Theory.redeclare_result states its contract); everything else, every fresh result
  above all, takes the stock export: a fresh result's hyps depend on whether its proof was
  forked*)
fun is_exported_form lthy th = null (Thm.hyps_of th) andalso Local_Theory.redeclaring lthy;

(*a theorem stored as it is stays the same object when this export would not change it,
  whatever its K; otherwise it is only generalised (light_export), nothing pasted*)
fun store_as_is lthy ctxt phi th =
  if Light_Locale_Axiom_Facts.unchanged_by phi th then th
  else Light_Locale_Axiom_Facts.light_export lthy ctxt th;

(*th' is th's copy in ctxt. For an untagged th, th' gets K = the number of premises the export
  from lthy to ctxt pastes on Drule.dummy_thm, which is the number pasted on th when every layer
  pastes the same number on every theorem; a tagged th gives th' itself, whose K Pure's own
  transformations already updated*)
fun put_premise_count lthy ctxt th th' =
  if Exported_Premises.count_of th = 0
  then Exported_Premises.put (Light_Locale_Axiom_Facts.export_premise_count lthy ctxt) th'
  else th';

fun light_morphism name write lthy ctxt =
  let val phi = Local_Theory.standard_morphism lthy ctxt in
    Light_Locale_Axiom_Facts.replace_fact name (fn th =>
      if is_exported_form lthy th then store_as_is lthy ctxt phi th
      else write lthy ctxt th (Morphism.thm phi th)) phi
    |> Morphism.set_context' lthy
  end;

(*copies kept inside the block: no writer -- an untagged theorem gets K only on its theory copy*)
val light_standard_morphism = light_morphism "Generic_Target.light_standard" (K (K (K I)));

val light_export_morphism = light_morphism "Generic_Target.light_export" put_premise_count;

fun background_abbrev (b, global_rhs) params =
  Local_Theory.background_theory_result (Sign.add_abbrev Print_Mode.internal (b, global_rhs))
  #>> apply2 (fn t => Term.list_comb (Logic.unvarify_global t, params))



(** nested local theories primitives **)

fun standard_facts lthy ctxt =
  Attrib.transform_facts (Local_Theory.standard_morphism lthy ctxt);

fun gen_standard_notes morph pred kind facts lthy =
  Local_Theory.map_contexts (fn level => fn ctxt =>
    if pred (Local_Theory.level lthy, level)
    then Attrib.local_notes kind (Attrib.transform_facts (morph lthy ctxt) facts) ctxt |> snd
    else ctxt) lthy;

val standard_notes = gen_standard_notes Local_Theory.standard_morphism;

fun gen_standard_declaration morphism pred decl lthy =
  Local_Theory.map_contexts (fn level => fn ctxt =>
    if pred (Local_Theory.level lthy, level)
    then Context.proof_map (Morphism.form (Morphism.transform (morphism lthy ctxt) decl)) ctxt
    else ctxt) lthy;

val standard_declaration = gen_standard_declaration Local_Theory.standard_morphism;
val light_standard_declaration = gen_standard_declaration light_standard_morphism;

fun standard_const pred prmode ((b, mx), rhs) =
  standard_declaration pred (const_decl (K true) prmode ((b, mx), rhs));

fun gen_standard_registration add pred registration lthy =
  Local_Theory.map_contexts (fn level =>
    if pred (Local_Theory.level lthy, level)
    then Context.proof_map (add registration)
    else I) lthy;

val standard_registration = gen_standard_registration Locale.add_registration;

val local_interpretation = standard_registration (fn (n, level) => level >= n - 1);



(** lifting target primitives to local theory operations **)

(* define *)

fun define foundation internal ((b, mx), ((b_def, atts), rhs)) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    (*term and type parameters*)
    val ((defs, _), rhs') = Thm.cterm_of lthy rhs
      |> Local_Defs.export_cterm lthy thy_ctxt ||> Thm.term_of;

    val xs = Variable.add_fixed lthy rhs' [];
    val T = Term.fastype_of rhs;
    val type_tfrees = TFrees.build (TFrees.add_tfreesT T #> fold (TFrees.add_tfreesT o #2) xs);
    val extra_tfrees =
      TFrees.build (rhs |> TFrees.add_tfrees_unless (TFrees.defined type_tfrees))
      |> TFrees.keys;
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
    val term_params = map Free (sort (Variable.fixed_ord lthy o apply2 #1) xs);
    val params = type_params @ term_params;

    val U = map Term.fastype_of params ---> T;

    (*foundation*)
    val ((lhs', global_def), lthy2) = lthy
      |> foundation (((b, U), mx'), (b_def, rhs')) (type_params, term_params);

    (*local definition*)
    val ([(lhs, (_, local_def))], lthy3) = lthy2
      |> Context_Position.set_visible false
      |> Local_Defs.define [((b, NoSyn), (Binding.empty_atts, lhs'))]
      ||> Context_Position.restore_visible lthy2;

    (*result*)
    val def =
      Thm.transitive local_def global_def
      |> Local_Defs.contract lthy3 defs (Thm.cterm_of lthy3 (Logic.mk_equals (lhs, rhs)));
    val ([(res_name, [res])], lthy4) = lthy3
      |> Local_Theory.notes [((if internal then Binding.empty else b_def, atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* notes *)

local

val name_thm1 = Global_Theory.name_thm Global_Theory.official1;
val name_thm2 = Global_Theory.name_thm Global_Theory.unofficial2;

fun thm_def (name, pos) thm lthy =
  if #1 name <> "" andalso Proofterm.zproof_enabled (Proofterm.get_proofs_level ()) then
    Local_Theory.background_theory_result (Thm.store_zproof (name, pos) thm) lthy
  else (thm, lthy);

fun thm_definition (name_pos, thm) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    (*export assumes/defines*)
    val ((defs, asms), thm') = Local_Defs.export lthy thy_ctxt thm;
    val asms' = map (rewrite_rule lthy (Drule.norm_hhf_eqs @ defs)) asms;

    (*export fixes*)
    val tfrees =
      TFrees.build (Thm.fold_terms {hyps = true} TFrees.add_tfrees thm')
      |> TFrees.keys |> map TFree;
    val frees =
      Frees.build (Thm.fold_terms {hyps = true} Frees.add_frees thm')
      |> Frees.list_set_rev |> map Free;
    val (schematic_thm :: variables) =
      (thm' :: map (Drule.mk_term o Thm.cterm_of lthy) (map Logic.mk_type tfrees @ frees))
      |> Variable.export lthy thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val (global_thm, lthy') = thm_def name_pos (name_thm1 name_pos schematic_thm) lthy;

    (*import fixes*)
    val (tvars, vars) =
      chop (length tfrees) (map (Thm.term_of o Drule.dest_term) variables)
      |>> map Logic.dest_type;

    val instT =
      TVars.build (fold2 (fn a => fn b =>
        (case a of TVar v => TVars.add (v, b) | _ => I)) tvars tfrees);
    val cinstT = TVars.map (K (Thm.ctyp_of lthy')) instT;
    val cinst =
      Vars.build
        (fold2 (fn v => fn t =>
          (case v of
            Var (xi, T) =>
              Vars.add ((xi, Term_Subst.instantiateT instT T),
                Thm.cterm_of lthy' (Term.map_types (Term_Subst.instantiateT_same instT) t))
          | _ => I)) vars frees);
    val fixed_thm = Thm.instantiate (cinstT, cinst) global_thm;

    (*import assumes/defines*)
    val local_thm =
      (fold (curry op COMP) asms' fixed_thm
        handle THM _ => raise THM ("Failed to re-import result", 0, fixed_thm :: asms'))
      |> Local_Defs.contract lthy defs (Thm.cprop_of thm)
      (*import assumes/defines: the kernel steps clear every tag; contract restores thm's
        proposition, so keep_count carries thm's K over*)
      |> Exported_Premises.keep_count thm
      |> Goal.norm_result lthy
      |> name_thm2 name_pos;

  in ((local_thm, global_thm), lthy') end;

(*export: a named theorem to its (local, global) pair*)
fun prepare_notes export facts lthy =
  let
    val (facts', lthy') =
      (facts, lthy) |-> fold_map (fn (a, thms) => fn lthy1 =>
        let
          val thms1 = Thm_Name.expr (Local_Theory.full_name_pos lthy1 (fst a)) thms;
          val (thms2, lthy2) =
            (thms1, lthy1) |-> fold_map (fn (args, atts) =>
              fold_map export args #>> rpair atts);
        in ((a, thms2), lthy2) end);
  in ((Attrib.map_thms #1 facts', Attrib.map_thms #2 facts'), lthy') end;

val unnamed = Binding.name "unnamed";

(*one group of evaluated entries per input fact, in order: the declaration entry split off by
  partial evaluation, if any, then the entry carrying the input's binding*)
fun regroup facts evaluated =
  let
    fun close entry (pending, groups) =
      if Binding.is_empty (#1 (#1 entry)) then (entry :: pending, groups)
      else ([], rev (entry :: pending) :: groups);
    val ([], groups) = fold close evaluated ([], []);
    fun rebind ((b, _), _) group =
      let val (decls, (_, fact)) = split_last group in decls @ [((b, []), fact)] end;
  in map2 rebind facts (rev groups) end;

in

fun notes target_notes kind facts lthy =
  let
    val ((local_facts, global_facts), lthy') =
      prepare_notes thm_definition (Attrib.map_thms (Goal.norm_result lthy) facts) lthy;
  in
    lthy'
    |> target_notes kind global_facts (Attrib.partial_evaluation lthy' local_facts)
    |> Attrib.local_notes kind local_facts
  end;

(*light target: theorems in exported form keep their statement, the others are exported as in
  a theory target and tagged with the number of exported premises; attributes are evaluated
  on the whole table once, in the block, the rest runs on the theory copies*)
fun light_notes locale kind facts lthy =
  let
    (*as stock notes: attributes see the normal form*)
    val groups =
      facts
      |> Attrib.map_thms (Goal.norm_result lthy)
      |> map (apfst (apfst (fn b => if Binding.is_empty b then unnamed else b)))
      |> Attrib.partial_evaluation lthy
      |> regroup facts;
    fun export (np, th) lthy1 =
      let val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy1) in
        if is_exported_form lthy1 th then
          let val phi = Local_Theory.standard_morphism lthy1 thy_ctxt in
            thm_def np (name_thm1 np (store_as_is lthy1 thy_ctxt phi th)) lthy1
            (*local copy: th as the attributes left it, as stock's local notes store it*)
            |>> pair (name_thm2 np th)
          end
        else
          let val th' = Goal.norm_result lthy1 th
          in thm_definition (np, th') lthy1 |>> apsnd (put_premise_count lthy1 thy_ctxt th') end
      end;
    val ((local_facts, global_facts), lthy') = prepare_notes export (flat groups) lthy;
    val hook_facts =
      unflat groups global_facts |> map (fn group => (#1 (List.last group), maps #2 group));
    val (results, lthy'') =
      lthy'
      |> Local_Theory.background_theory (Attrib.global_notes kind global_facts #> snd)
      |> tap (fn lthy2 =>
          (case Locale.light_degeneracy_check_of (Proof_Context.theory_of lthy2) of
            SOME check => check locale hook_facts lthy2
          | NONE => ()))
      |> gen_standard_notes light_standard_morphism (op <>) kind local_facts
      |> Attrib.local_notes kind local_facts;
  in (map List.last (unflat groups results), lthy'') end;

end;


(* abbrev *)

fun abbrev target_abbrev prmode ((b, mx), rhs) lthy =
  let
    val (global_rhs, (extra_tfrees, (type_params, term_params))) = export_abbrev lthy I rhs;
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;
  in
    lthy
    |> target_abbrev prmode (b, mx') global_rhs (type_params, term_params)
    |> Context_Position.set_visible false
    |> Proof_Context.add_abbrev Print_Mode.internal (b, rhs) |> snd
    |> Local_Defs.fixed_abbrev ((b, NoSyn), rhs)
    ||> Context_Position.restore_visible lthy
  end;



(** theory target primitives **)

fun theory_target_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  background_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => standard_const (op <>) Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def));

fun theory_target_notes kind global_facts local_facts =
  Local_Theory.background_theory (Attrib.global_notes kind global_facts #> snd)
  #> standard_notes (op <>) kind local_facts;

fun theory_target_abbrev prmode (b, mx) global_rhs params =
  Local_Theory.background_theory_result
    (Sign.add_abbrev (#1 prmode) (b, global_rhs) #->
      (fn (lhs, _) =>  (* FIXME type_params!? *)
        Sign.notation_global true prmode
          [(lhs, check_mixfix_global (b, null (snd params)) mx)] #> pair lhs))
  #-> (fn lhs =>
        standard_const (op <>) prmode
          ((b, if null (snd params) then NoSyn else mx),
            Term.list_comb (Logic.unvarify_global lhs, snd params)));



(** theory operations **)

val theory_abbrev = abbrev theory_target_abbrev;

fun theory_declaration decl =
  background_declaration decl #> standard_declaration (K true) decl;

fun light_theory_declaration decl =
  gen_background_declaration light_export_morphism decl #>
  light_standard_declaration (K true) decl;

fun target_registration lthy {inst, mixin, export} =
  {inst = inst, mixin = mixin,
    export = export $> Proof_Context.export_morphism lthy (Local_Theory.target_of lthy)};

fun theory_registration registration lthy =
  lthy
  |> (Local_Theory.raw_theory o Context.theory_map)
    (Locale.add_registration (target_registration lthy registration))
  |> standard_registration (K true) registration;



(** locale target primitives **)

fun locale_target_notes locale kind global_facts local_facts =
  Local_Theory.background_theory
    (Attrib.global_notes kind (Attrib.map_facts (K []) global_facts) #> snd) #>
  (fn lthy => lthy |>
    Local_Theory.target (fn ctxt => ctxt |>
      Locale.add_facts locale kind (standard_facts lthy ctxt local_facts))) #>
  standard_notes (fn (this, other) => other <> 0 andalso this <> other) kind local_facts;

fun locale_target_declaration locale params decl lthy = lthy
  |> Local_Theory.target (fn ctxt => ctxt |>
    Locale.add_declaration locale params
      (Morphism.transform (Local_Theory.standard_morphism lthy ctxt) decl));

fun locale_target_const locale phi_pred prmode ((b, mx), rhs) =
  locale_target_declaration locale {syntax = true, pos = Binding.pos_of b}
    (const_decl phi_pred prmode ((b, mx), rhs));


(** locale operations **)

fun locale_declaration locale {syntax, pervasive, pos} decl =
  pervasive ? background_declaration decl
  #> locale_target_declaration locale {syntax = syntax, pos = pos} decl
  #> standard_declaration (fn (_, other) => other <> 0) decl;

fun locale_const locale prmode ((b, mx), rhs) =
  locale_target_const locale (K true) prmode ((b, mx), rhs)
  #> standard_const (fn (this, other) => other <> 0 andalso this <> other) prmode ((b, mx), rhs);

fun gen_locale_dependency add loc registration lthy =
  lthy
  |> Local_Theory.raw_theory (Locale.add_dependency loc registration)
  |> gen_standard_registration add (K true) registration;

val locale_dependency = gen_locale_dependency Locale.add_registration;


(** locale abbreviations **)

fun locale_target_abbrev locale prmode (b, mx) global_rhs params =
  background_abbrev (b, global_rhs) (snd params)
  #-> (fn (lhs, _) => locale_const locale prmode ((b, mx), lhs));

fun locale_abbrev locale = abbrev (locale_target_abbrev locale);

end;
