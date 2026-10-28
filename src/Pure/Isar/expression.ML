(*  Title:      Pure/Isar/expression.ML
    Author:     Clemens Ballarin, TU Muenchen

Locale expressions and user interface layer of locales.
*)

signature EXPRESSION =
sig
  (* Locale expressions *)
  datatype 'term map = Positional of 'term option list | Named of (string * 'term) list
  type 'term rewrites = (Attrib.binding * 'term) list
  type ('name, 'term) expr = ('name * ((string * bool) * ('term map * 'term rewrites))) list
  type expression_i = (string, term) expr * (binding * typ option * mixfix) list
  type expression = (xstring * Position.T, string) expr * (binding * string option * mixfix) list

  (* Processing of context statements *)
  val cert_statement: Element.context_i list -> Element.statement_i ->
    Proof.context -> (Attrib.binding * (term * term list) list) list * Proof.context
  val read_statement: Element.context list -> Element.statement ->
    Proof.context -> (Attrib.binding * (term * term list) list) list * Proof.context

  (* Declaring locales *)
  val cert_declaration: expression_i -> (Proof.context -> Proof.context) ->
    Element.context_i list ->
    Proof.context -> (((string * typ) * mixfix) list * (string * morphism) list
      * Element.context_i list * Proof.context) * ((string * typ) list * Proof.context)
  val cert_read_declaration: expression_i -> (Proof.context -> Proof.context) ->
    Element.context list ->
    Proof.context -> (((string * typ) * mixfix) list * (string * morphism) list
      * Element.context_i list * Proof.context) * ((string * typ) list * Proof.context)
      (*FIXME*)
  val read_declaration: expression -> (Proof.context -> Proof.context) -> Element.context list ->
    Proof.context -> (((string * typ) * mixfix) list * (string * morphism) list
      * Element.context_i list * Proof.context) * ((string * typ) list * Proof.context)
  val add_locale: binding -> binding -> Bundle.name list ->
    expression_i -> Element.context_i list -> theory -> string * local_theory
  val add_locale_cmd: binding -> binding -> Bundle.xname list ->
    expression -> Element.context list -> theory -> string * local_theory
  val add_light_locale: binding -> binding -> Bundle.name list ->
    expression_i -> term Syntax_Trans.implicit_structure_spec -> Element.context_i list ->
    theory -> string * local_theory
  val add_light_locale_cmd: binding -> binding -> Bundle.xname list ->
    expression -> string Syntax_Trans.implicit_structure_spec -> Element.context list ->
    theory -> string * local_theory

  (* Light locale headers: eliminated parameters, unfolded definitions *)
  val eliminated_params: theory -> string -> (string * int * term) list
  val unfolded_definitions: Proof.context -> string -> (string * (string * term)) list
  val unfolded_definitions_message: Proof.context -> string -> string list

  (* Processing of locale expressions *)
  val cert_goal_expression: expression_i -> Proof.context ->
    (term list list * term list list * (string * morphism) list * (Attrib.binding * term) list list * morphism) * Proof.context
  val read_goal_expression: expression -> Proof.context ->
    (term list list * term list list * (string * morphism) list * (Attrib.binding * term) list list * morphism) * Proof.context
end;

structure Expression : EXPRESSION =
struct

datatype ctxt = datatype Element.ctxt;


(*** Expressions ***)

datatype 'term map =
  Positional of 'term option list |
  Named of (string * 'term) list;

type 'term rewrites = (Attrib.binding * 'term) list;

type ('name, 'term) expr = ('name * ((string * bool) * ('term map * 'term rewrites))) list;

type expression_i = (string, term) expr * (binding * typ option * mixfix) list;
type expression = (xstring * Position.T, string) expr * (binding * string option * mixfix) list;


(** Internalise locale names in expr **)

fun check_expr ctxt instances = map (apfst (Locale.check ctxt)) instances;


(** Parameters of expression **)

(*The parameters of loc that its defines clauses define: name, 1-based position in
  Locale.params_of, definition body (not normalised).  A light header eliminates these
  positions (plan decision 1); a light locale stores no defs, so it has none.*)

fun eliminated_params thy loc =
  let val params = Locale.params_of thy loc in
    #2 (Locale.specification_of thy loc)
    |> map_filter (fn eq =>
      let val ((y, _), b) = Local_Defs.abs_def eq in
        (case find_index (fn ((x, _), _) => x = y) params of
          ~1 => NONE
        | j => SOME (y, j + 1, b))
      end)
    |> sort (int_ord o apply2 #2)
  end;

(*Sanity check of instantiations and extraction of implicit parameters.
  The latter only occurs iff strict = false.
  Positional instantiations are extended to match full length of parameter list
  of instantiated locale.
  A light header treats the eliminated positions as instantiated, whatever is written there,
  and records the kind of every position (plan section 3.2 item 4, decision 16 (b)).*)

fun parameters_of thy strict light (expr, fixed) =
  let
    val ctxt = Proof_Context.init_global thy;

    fun eliminated loc = if light then map #1 (eliminated_params thy loc) else [];

    fun reject_dups message xs =
      (case duplicates (op =) xs of
        [] => ()
      | dups => error (message ^ commas dups));

    fun parm_eq ((p1, mx1), (p2, mx2)) =
      p1 = p2 andalso
        (Mixfix.equal (mx1, mx2) orelse
          error ("Conflicting syntax for parameter " ^ quote p1 ^ " in expression" ^
            Position.here_list [Mixfix.pos_of mx1, Mixfix.pos_of mx2]));

    fun params_loc loc = Locale.params_of thy loc |> map (apfst #1);
    fun params_inst (loc, (prfx, (Positional insts, eqns))) =
          let
            val ps = params_loc loc;
            val d = length ps - length insts;
            val insts' =
              if d < 0 then
                error ("More arguments than parameters in instantiation of locale " ^
                  quote (Locale.markup_name ctxt loc))
              else insts @ replicate d NONE;
            val elim = eliminated loc;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => if member (op =) elim (#1 p) then NONE else SOME p
                | (_, SOME _) => NONE);
            val kinds = (ps ~~ insts') |> map (fn ((p, _), inst) =>
              if member (op =) elim p then Locale.Eliminated
              else if is_some inst then Locale.Written else Locale.Inherited);
          in ((ps', kinds), (loc, (prfx, (Positional insts', eqns)))) end
      | params_inst (loc, (prfx, (Named insts, eqns))) =
          let
            val _ =
              reject_dups "Duplicate instantiation of the following parameter(s): "
                (map fst insts);
            val elim = eliminated loc;
            val ps' = (insts, params_loc loc) |-> fold (fn (p, _) => fn ps =>
              if AList.defined (op =) ps p then AList.delete (op =) p ps
              else error (quote p ^ " not a parameter of instantiated expression"))
              |> filter_out (member (op =) elim o #1);
            val kinds = params_loc loc |> map (fn (p, _) =>
              if member (op =) elim p then Locale.Eliminated
              else if AList.defined (op =) insts p then Locale.Written else Locale.Inherited);
          in ((ps', kinds), (loc, (prfx, (Named insts, eqns)))) end;
    fun params_expr is =
      let
        val ((is', kindss), ps') = fold_map (fn i => fn ps =>
          let
            val ((ps', kinds), i') = params_inst i;
            val ps'' = distinct parm_eq (ps @ ps');
          in ((i', kinds), ps'') end) is []
          |>> split_list;
      in (ps', is', kindss) end;

    val (implicit, expr', kindss) = params_expr expr;

    val implicit' = map #1 implicit;
    val fixed' = map (Variable.check_name o #1) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val implicit'' =
      if strict then []
      else
        let
          val _ =
            reject_dups
              "Parameter(s) declared simultaneously in expression and for clause: "
              (implicit' @ fixed');
        in map (fn (x, mx) => (Binding.name x, NONE, mx)) implicit end;

  in (expr', implicit'' @ fixed, kindss) end;


(** Read instantiation **)

(* Parse positional or named instantiation *)

local

fun prep_inst prep_term ctxt parms (Positional insts) =
      (insts ~~ parms) |> map
        (fn (NONE, p) => Free (p, dummyT)
          | (SOME t, _) => prep_term ctxt t)
  | prep_inst prep_term ctxt parms (Named insts) =
      parms |> map (fn p =>
        (case AList.lookup (op =) insts p of
          SOME t => prep_term ctxt t |
          NONE => Free (p, dummyT)));

in

fun parse_inst x = prep_inst Syntax.parse_term x;
fun make_inst x = prep_inst (K I) x;

end;


(* Instantiation morphism *)

fun inst_morphism params ((prfx, mandatory), insts') ctxt =
  let
    (* parameters *)
    val parm_types = map #2 params;
    val type_parms = fold Term.add_tfreesT parm_types [];

    (* type inference *)
    val parm_types' = map (Type_Infer.paramify_vars o Logic.varifyT_global) parm_types;
    val type_parms' = fold Term.add_tvarsT parm_types' [];
    val checked =
      (map (Logic.mk_type o TVar) type_parms' @ map2 Type.constraint parm_types' insts')
      |> Syntax.check_terms (Config.put Type_Infer.object_logic false ctxt)
    val (type_parms'', insts'') = chop (length type_parms') checked;

    (* context *)
    val ctxt' = fold Proof_Context.augment checked ctxt;
    val certT = Thm.trim_context_ctyp o Thm.ctyp_of ctxt';
    val cert = Thm.trim_context_cterm o Thm.cterm_of ctxt';

    (* instantiation *)
    val instT =
      TFrees.build
        (fold2 (fn v => fn T => not (TFree v = T) ? TFrees.add (v, T))
          type_parms (map Logic.dest_type type_parms''));
    val cert_inst =
      Frees.build
        (fold2 (fn v => fn t => not (Free v = t) ? Frees.add (v, cert t))
          (map #1 params ~~ map (Term_Subst.instantiateT_frees instT) parm_types) insts'');
  in
    (Element.instantiate_normalize_morphism (TFrees.map (K certT) instT, cert_inst) $>
      Morphism.binding_morphism "Expression.inst" (Binding.prefix mandatory prfx), ctxt')
  end;


(** Light headers: eliminated positions (plan section 3.2 items 4 and 5) **)

val norm_term = Envir.beta_norm oo Term.subst_atomic;

(*the type variables named in names become schematic at index i, then inference parameters;
  other TFrees stay*)
fun paramify_at i names =
  Term.map_type_tfree (fn (x, S) => if member (op =) names x then TVar ((x, i), S) else TFree (x, S))
  #> Type_Infer.paramify_vars;

(*the type variables of a locale's parameter types: those the import at index i makes its
  inference parameters*)
fun import_type_names thy loc =
  map #1 (fold (Term.add_tfreesT o #2 o #1) (Locale.params_of thy loc) []);

(*strip the constraints decode_term wraps around atomic position markup (syntax_phases.ML),
  so that a bare underscore shows*)
fun strip_position_constraints (t as Const ("_type_constraint_", Type ("fun", [T, _])) $ u) =
      if Term_Position.detect_positionT T then strip_position_constraints u else t
  | strip_position_constraints t = t;

fun ordinal n =
  string_of_int n ^
    (if n mod 100 div 10 = 1 then "th"
     else (case n mod 10 of 1 => "st" | 2 => "nd" | 3 => "rd" | _ => "th"));

(*steps (a) and (b) of plan section 3.2 item 4: the bodies of the eliminated parameters
  normalised in the parent's vocabulary -- the fixed environment env0 applied length elims times;
  a body that still mentions an eliminated name means the parent's defines have a cycle
  (substitution and beta reduction only remove names), reported with the section 6 definition
  message, which lists the definitions of the first cycle in parameter order, printed from their
  original bodies*)
fun normalise_eliminated ctxt loc elims =
  let
    val params = map #1 (Locale.params_of (Proof_Context.theory_of ctxt) loc);
    val eliminated = map #1 elims;
    fun mentioned t = inter (op =) (Term.add_free_names t []) eliminated;
    fun subst env = norm_term (map (apfst Free) env);
    val env0 =
      fold (fn (y, j, b) => fn env => ((y, #2 (nth params (j - 1))), subst env b) :: env) elims []
      |> rev;
    val env = funpow (length elims) (map (apsnd (subst env0))) env0;
    val _ =
      if exists (not o null o mentioned o #2) env then
        let
          val graph = String_Graph.make (map (fn (y, _, b) => ((y, ()), mentioned b)) elims);
          fun reaches y z =
            member (op =) (String_Graph.all_succs graph (String_Graph.immediate_succs graph y)) z;
          val y0 = the (find_first (fn y => reaches y y) eliminated);
          val defs = elims |> filter (fn (y, _, _) => reaches y0 y andalso reaches y y0)
            |> map (fn (y, _, b) => "`" ^ y ^ " \<equiv> " ^ Syntax.string_of_term ctxt b ^ "`");
          val listed = commas (take (length defs - 1) defs) ^ " and " ^ List.last defs;
        in
          error ("A light locale does not support definitions. The definitions " ^ listed ^
            " from locale `" ^ Locale.extern ctxt loc ^
            "` refer to each other in a cycle and cannot be unfolded.")
        end
      else ();
  in map2 (fn (y, j, _) => fn (_, b) => (y, j, b)) elims env end;


(*** Locale processing ***)

(** Parsing **)

fun parse_elem prep_typ prep_term ctxt =
  Element.map_ctxt
   {binding = I,
    typ = prep_typ ctxt,
    term = prep_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt),
    pattern = prep_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt),
    fact = I,
    attrib = I};

fun prepare_stmt prep_prop prep_obtains ctxt stmt =
  (case stmt of
    Element.Shows raw_shows =>
      raw_shows |> (map o apsnd o map) (fn (t, ps) =>
        (prep_prop (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t,
          map (prep_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) ps))
  | Element.Obtains raw_obtains =>
      let
        val ((_, thesis), thesis_ctxt) = Obtain.obtain_thesis ctxt;
        val obtains = prep_obtains thesis_ctxt thesis raw_obtains;
      in map (fn (b, t) => ((b, []), [(t, [])])) obtains end);


(** Simultaneous type inference: instantiations + elements + statement **)

local

fun mk_type T = (Logic.mk_type T, []);
fun mk_term t = (t, []);
fun mk_propp (p, pats) = (Type.constraint propT p, pats);

fun dest_type (T, []) = Logic.dest_type T;
fun dest_term (t, []) = t;
fun dest_propp (p, pats) = (p, pats);

fun extract_inst (_, (_, ts)) = map mk_term ts;
fun restore_inst ((l, (p, _)), cs) = (l, (p, map dest_term cs));

fun extract_eqns es = map (mk_term o snd) es;
fun restore_eqns (es, cs) = map2 (fn (b, _) => fn c => (b, dest_term c)) es cs;

fun extract_elem (Fixes fixes) = map (#2 #> the_list #> map mk_type) fixes
  | extract_elem (Constrains csts) = map (#2 #> single #> map mk_type) csts
  | extract_elem (Assumes asms) = map (#2 #> map mk_propp) asms
  | extract_elem (Defines defs) = map (fn (_, (t, ps)) => [mk_propp (t, ps)]) defs
  | extract_elem (Notes _) = []
  | extract_elem (Lazy_Notes _) = [];

fun restore_elem (Fixes fixes, css) =
      (fixes ~~ css) |> map (fn ((x, _, mx), cs) =>
        (x, cs |> map dest_type |> try hd, mx)) |> Fixes
  | restore_elem (Constrains csts, css) =
      (csts ~~ css) |> map (fn ((x, _), cs) =>
        (x, cs |> map dest_type |> hd)) |> Constrains
  | restore_elem (Assumes asms, css) =
      (asms ~~ css) |> map (fn ((b, _), cs) => (b, map dest_propp cs)) |> Assumes
  | restore_elem (Defines defs, css) =
      (defs ~~ css) |> map (fn ((b, _), [c]) => (b, dest_propp c)) |> Defines
  | restore_elem (elem as Notes _, _) = elem
  | restore_elem (elem as Lazy_Notes _, _) = elem;

fun prep (_, pats) (ctxt, t :: ts) =
  let val ctxt' = Proof_Context.augment t ctxt
  in
    ((t, Syntax.check_props (Proof_Context.set_mode Proof_Context.mode_pattern ctxt') pats),
      (ctxt', ts))
  end;

fun check cs ctxt =
  let
    val (cs', (ctxt', _)) = fold_map prep cs
      (ctxt, Syntax.check_terms
        (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) (map fst cs));
  in (cs', ctxt') end;

in

(*extras: further terms typed jointly -- a light header's implicit structure*)
fun check_autofix' insts eqnss elems concl extras ctxt =
  let
    val inst_cs = map extract_inst insts;
    val eqns_cs = map extract_eqns eqnss;
    val elem_css = map extract_elem elems;
    val concl_cs = (map o map) mk_propp (map snd concl);
    val extra_cs = [map mk_term extras];
    (* Type inference *)
    val (inst_cs' :: eqns_cs' :: css', ctxt') =
      (fold_burrow o fold_burrow) check
        (inst_cs :: eqns_cs :: elem_css @ [concl_cs, extra_cs]) ctxt;
    val (elem_css', [concl_cs', extra_cs']) = chop (length elem_css) css';
  in
    ((map restore_inst (insts ~~ inst_cs'),
      map restore_eqns (eqnss ~~ eqns_cs'),
      map restore_elem (elems ~~ elem_css'),
      map fst concl ~~ concl_cs',
      map dest_term (flat extra_cs')), ctxt')
  end;

fun check_autofix insts eqnss elems concl ctxt =
  let val ((insts', eqnss', elems', concl', _), ctxt') =
    check_autofix' insts eqnss elems concl [] ctxt
  in ((insts', eqnss', elems', concl'), ctxt') end;

end;


(** Prepare locale elements **)

(*the names a header's for clause and fixes elements write, from the text (the parameters would
  carry inherited Structure mixfixes), each with its mixfix*)
fun fixes_names fixes = map (fn (b, _, mx) => (Binding.name_of b, mx)) fixes;
fun header_names raw_import raw_elems =
  fixes_names (#2 raw_import) @
    maps (fn Element.Fixes fixes => fixes_names fixes | _ => []) raw_elems;

(*the (structure) parameters a header writes itself*)
fun header_structure_names raw_import raw_elems =
  header_names raw_import raw_elems |> map_filter (fn (x, Mixfix.Structure _) => SOME x | _ => NONE);

fun declare_elem prep_var (Fixes fixes) ctxt =
      let val (vars, _) = fold_map prep_var fixes ctxt
      in ctxt |> Proof_Context.add_fixes vars |> snd end
  | declare_elem prep_var (Constrains csts) ctxt =
      ctxt |> fold_map (fn (x, T) => prep_var (Binding.name x, SOME T, NoSyn)) csts |> snd
  | declare_elem _ (Assumes _) ctxt = ctxt
  | declare_elem _ (Defines _) ctxt = ctxt
  | declare_elem _ (Notes _) ctxt = ctxt
  | declare_elem _ (Lazy_Notes _) ctxt = ctxt;


(** Finish locale elements **)

fun finish_inst ctxt (loc, (prfx, inst)) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (morph, _) = inst_morphism (map #1 (Locale.params_of thy loc)) (prfx, inst) ctxt;
  in (loc, morph) end;

fun finish_fixes (parms: (string * typ) list) = map (fn (binding, _, mx) =>
  let val x = Binding.name_of binding
  in (binding, AList.lookup (op =) parms x, mx) end);

local

fun closeup _ _ false elem = elem
  | closeup (outer_ctxt, ctxt) parms true elem =
      let
        (* FIXME consider closing in syntactic phase -- before type checking *)
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if Variable.is_fixed outer_ctxt x orelse AList.defined (op =) parms x then I
                else insert (op =) (x, T) | _ => I) t [];
          in fold (Logic.all o Free) rev_frees t end;

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in context element";
      in
        (case elem of
          Assumes asms => Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Defines defs => Defines (defs |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = Local_Defs.cert_def ctxt (K []) (close_frees t)
            in ((Thm.def_binding_optional (Binding.name c) name, atts), (t', no_binds ps)) end))
        | e => e)
      end;

in

fun finish_elem _ parms _ (Fixes fixes) = Fixes (finish_fixes parms fixes)
  | finish_elem _ _ _ (Constrains _) = Constrains []
  | finish_elem ctxts parms do_close (Assumes asms) = closeup ctxts parms do_close (Assumes asms)
  | finish_elem ctxts parms do_close (Defines defs) = closeup ctxts parms do_close (Defines defs)
  | finish_elem _ _ _ (elem as Notes _) = elem
  | finish_elem _ _ _ (elem as Lazy_Notes _) = elem;

end;


(** Process full context statement: instantiations + elements + statement **)

(* Interleave incremental parsing and type inference over entire parsed stretch. *)

local

fun abs_def ctxt =
  Thm.cterm_of ctxt #> Assumption.assume ctxt #> Local_Defs.abs_def_rule ctxt #> Thm.prop_of;

(*the filled eliminated positions are stored as the image of the parent's definition body
  under the morphism of the checked instance -- the value stock eval_inst computes
  (plan section 3.2 item 4 (d)); imports without filled positions are untouched*)
fun finish_deps ctxt5 insts filled =
  let
    val deps0 = map (finish_inst ctxt5) insts;
    fun refill (_, dep) [] = dep
      | refill ((loc, (prfx, ts)), (_, m)) entries =
          finish_inst ctxt5
            (loc, (prfx, fold (fn (j, body) => nth_map j (K (Morphism.term m body))) entries ts));
  in map2 refill (insts ~~ deps0) filled end;

fun prep_full_context_statement
    parse_typ parse_prop parse_term prep_obtains prep_var_elem prep_inst prep_eqns prep_attr
    prep_var_inst prep_expr
    {strict, do_close, fixed_frees, light} raw_import structure_spec init_body raw_elems raw_stmt
    ctxt1 =
  let
    val thy = Proof_Context.theory_of ctxt1;

    val (raw_insts, fixed, kindss) =
      parameters_of thy strict light (apfst (prep_expr ctxt1) raw_import);

    (*fold state: index, instances, rewrites, context, and per import the eliminated positions
      not kept (0-based position, the parent's normalised definition body), which finish_deps
      stores as the unfolded term*)
    fun prep_insts_cumulative (loc, (prfx, (inst, eqns))) (i, insts, eqnss, ctxt, filled) =
      let
        val params = map #1 (Locale.params_of thy loc);
        val inst' = prep_inst ctxt (map #1 params) inst;
        val type_names = import_type_names thy loc;
        val parm_types' = map (paramify_at i type_names o #2) params;

        (* eliminated positions of a light header (plan section 3.2 item 4) *)
        val elims = if light then normalise_eliminated ctxt loc (eliminated_params thy loc) else [];
        val (inst', filled') =
          if null elims then (inst', [])
          else
            let
              val eliminated = map #1 elims;

              (* (c) the parent's type variables at this index, then the non-eliminated parameters
                 replaced by their terms in inst', each under the type of the Free it replaces *)
              val param_inst = (map #1 params ~~ inst') |> filter_out (member (op =) eliminated o #1);
              fun substitute b =
                b |> Term.map_types (paramify_at i type_names)
                  |> Term.map_aterms (fn Free (p, T) =>
                      (case AList.lookup (op =) param_inst p of
                        SOME t => Type.constraint T t
                      | NONE => Free (p, T)) | a => a);
              val substituted = fold (fn (_, j, b) => nth_map (j - 1) (K (substitute b))) elims inst';
              fun written y j =
                (case inst of
                  Positional xs => is_some (nth xs (j - 1))
                | Named xs => AList.defined (op =) xs y);
              fun constrained ts = (loc, (prfx, map2 Type.constraint parm_types' ts));

              (* a written position is checked jointly with the substituted term: accepted iff
                 they are equal up to beta, eta and types; kept (the user's term stays) iff equal
                 including types; otherwise the substituted term is filled in *)
              fun keeps (y, j, _) =
                let val t = nth inst' (j - 1) in
                  written y j andalso not (Term.is_dummy_pattern (strip_position_constraints t))
                  andalso
                    let
                      val copies = map constrained [nth_map (j - 1) (K t) substituted, substituted];
                      val ((checked_insts, _, _, _), _) =
                        check_autofix (insts @ copies) [] [] [] ctxt;
                      val checked_copies = map (#2 o #2) (drop (length insts) checked_insts);
                      val checked = Envir.beta_eta_contract (nth (hd checked_copies) (j - 1));
                      val shown = Envir.beta_norm (nth (List.last checked_copies) (j - 1));
                      val shown' = Envir.beta_eta_contract shown;
                    in
                      if Term.aconv_untyped (checked, shown') then checked aconv shown'
                      else
                        error ("The " ^ ordinal j ^ " parameter `" ^ y ^ "` of locale `" ^
                          Locale.extern ctxt loc ^ "` is defined as `" ^
                          Syntax.string_of_term ctxt shown ^
                          "` and cannot be instantiated. You must write `_`.")
                    end
                end;
              val decisions = map (fn e => (e, keeps e)) elims;
              val decided =
                fold (fn ((_, j, _), kept) => not kept ? nth_map (j - 1) (K (nth substituted (j - 1))))
                  decisions inst';
            in
              (decided, map_filter (fn ((_, j, b), kept) => if kept then NONE else SOME (j - 1, b)) decisions)
            end;

        val inst'' = map2 Type.constraint parm_types' inst';
        val insts' = insts @ [(loc, (prfx, inst''))];
        (*the names this import eliminates join the context's table of eliminated names (plan
          decision 1, D20): from here on the check stage warns of them -- in this and the later
          instances and in the elements -- as it warns of a light ancestor's; the value is the
          constrained instance at the eliminated position, whose type is the parameter's*)
        val ctxt = ctxt |> Context.proof_map (Locale.eliminated_names_declaration
          (map (fn (y, j, _) => (y, (loc, nth inst'' (j - 1)))) elims) Morphism.identity);
        val ((insts'', _, _, _), ctxt2) = check_autofix insts' [] [] [] ctxt;
        val inst''' = insts'' |> List.last |> snd |> snd;
        val (inst_morph, _) = inst_morphism params (prfx, inst''') ctxt;
        val ctxt' = Locale.activate_declarations (loc, inst_morph) ctxt2
          handle ERROR msg => if null eqns then error msg else
            (Locale.tracing ctxt1
             (msg ^ "\nFalling back to reading rewrites clause before activation.");
             ctxt2);

        val attrss = map (apsnd (map (prep_attr ctxt)) o fst) eqns;
        val eqns' = (prep_eqns ctxt' o map snd) eqns;
        val eqnss' = [attrss ~~ eqns'];
        val ((_, [eqns''], _, _), _) = check_autofix insts'' eqnss' [] [] ctxt';
        val rewrite_morph = eqns'
          |> map (abs_def ctxt')
          |> Variable.export_terms ctxt' ctxt
          |> Element.eq_term_morphism ctxt
          |> Morphism.default;
       val ctxt'' = Locale.activate_declarations (loc, inst_morph $> rewrite_morph) ctxt;
       val eqnss' = eqnss @ [attrss ~~ Variable.export_terms ctxt' ctxt eqns'];
      in (i + 1, insts', eqnss', ctxt'', filled @ [filled']) end;

    fun prep_elem raw_elem ctxt =
      let
        val ctxt' = ctxt
          |> Context_Position.set_visible false
          |> declare_elem prep_var_elem raw_elem
          |> Context_Position.restore_visible ctxt;
        val elems' = parse_elem parse_typ parse_prop ctxt' raw_elem;
      in (elems', ctxt') end;

    val fors = fold_map prep_var_inst fixed ctxt1 |> fst;
    val ctxt2 = ctxt1 |> Proof_Context.add_fixes fors |> snd;
    val (_, insts', eqnss', ctxt3, filled) =
      fold prep_insts_cumulative raw_insts (0, [], [], ctxt2, []);

    (* the implicit structure of the header (plan section 3.2 item 6; header plan section 3.3):
       structure_spec is the header's own element, Declare t, Cancel or Inherit.  imports_state is
       how a bare index position reads without the element: the imports' cut (import i's term in
       its own vocabulary), the first surviving variable structure h where a cancelled slot is
       reachable, cancelled, or inherited -- unless the outer context has a declared implicit
       structure, which a goal expression keeps whatever its imports give.  Under Declare, t and
       the body's bare index positions share the inference parameter T_ph. *)
    val locs = map #1 raw_insts;
    val imports_state =
      if is_some (Syntax_Trans.implicit_structure ctxt3) then Locale.Inherited_Structure
      else
        Locale.imports_structure_state thy (header_structure_names raw_import raw_elems)
          (locs ~~ kindss);
    val placeholder = Free (Syntax_Trans.implicit_structure_, dummyT);
    val declare_placeholder = Proof_Context.declare_implicit_structure placeholder;
    val decl_ = Name.internal "declared_structure";
    val T_ph = Type_Infer.param (length locs) ("'struct", []);
    fun map_free x f = Term.map_aterms (fn a as Free (y, _) => if y = x then f a else a | a => a);
    val map_placeholder = map_free Syntax_Trans.implicit_structure_;
    fun map_elems f =
      map (Element.map_ctxt {binding = I, typ = I, term = f, pattern = f, fact = I, attrib = I});
    val cancel = Syntax_Trans.put_implicit_structure Syntax_Trans.Cancel;
    (*reading under the imports: the context, and what the placeholder occurrences of a term read
      there become.  Under a cut each occurrence is constrained by the cut's type with import i's
      parameter type variables as that import's inference parameters (index i, as in
      prep_insts_cumulative; its other type variables stay rigid) and named x: the placeholder for
      the body, decl_ for t, since one joint check gives every Free of one name one type and the
      body's bare positions (t) and t's own (the cut) differ -- a type error at such a position of
      t prints decl_ (header plan section 3.3).  Under h the occurrence becomes h before the
      check, which types h with the rest*)
    fun imports_reading x =
      (case imports_state of
        Locale.Structure_Of (i, t_src) =>
          let val T_par = paramify_at i (import_type_names thy (nth locs i)) (Term.fastype_of t_src)
          in (declare_placeholder, map_placeholder (K (Type.constraint T_par (Free (x, dummyT))))) end
      | Locale.Structure_Head h => (declare_placeholder, map_placeholder (K (Free (h, dummyT))))
      | Locale.Cancelled_Structure => (cancel, I)
      | Locale.Inherited_Structure => (I, I));
    (*one case on the element: how the body reads bare index positions -- under Declare as the
      untyped placeholder constrained by T_ph (the printer drops it, so a type error shows the bare
      position), under Cancel as an error, under Inherit as the imports give -- and how t is read:
      after all elements, with the body's reading taken out and the imports' put in*)
    val ((body_install, body_constrain), read_structure) =
      (case structure_spec of
        Syntax_Trans.Declare t_raw =>
          let
            val (install, constrain) = imports_reading decl_;
            fun read ctxt =
              let val ctxt' = ctxt |> Syntax_Trans.put_implicit_structure Syntax_Trans.Inherit |> install
              in [Type.constraint T_ph (constrain (parse_term ctxt' t_raw))] end;
          in
            ((declare_placeholder #> Variable.add_fixes_direct [decl_],
              map_placeholder (Type.constraint T_ph)), read)
          end
      | Syntax_Trans.Cancel => ((cancel, I), K [])
      | Syntax_Trans.Inherit => (imports_reading Syntax_Trans.implicit_structure_, K []));

    fun prep_stmt elems ctxt =
      check_autofix' insts' [] elems (prepare_stmt parse_prop prep_obtains ctxt raw_stmt)
        (read_structure ctxt) ctxt;

    val _ =
      if fixed_frees then ()
      else
        (case fold (fold (Variable.add_frees ctxt3) o snd o snd) insts' [] of
          [] => ()
        | frees => error ("Illegal free variables in expression: " ^
            commas_quote (map (Syntax.string_of_term ctxt3 o Free) (rev frees))));

    val ((insts, _, elems', concl, structures), ctxt4) = ctxt3
      |> body_install
      |> init_body
      |> fold_map prep_elem raw_elems
      |>> map_elems body_constrain
      |-> prep_stmt;


    (* parameters from expression and elements *)

    val xs = maps (fn Fixes fixes => map (Variable.check_name o #1) fixes | _ => [])
      (Fixes fors :: elems');
    val (parms, ctxt5) = fold_map Proof_Context.inferred_param xs ctxt4;

    val fors' = finish_fixes parms fors;
    val fixed = map (fn (b, SOME T, mx) => ((Binding.name_of b, T), mx)) fors';
    val deps = finish_deps ctxt5 insts filled;

    (*one case on the element: the final structure state and the slot value in the final
      vocabulary, and what the body's bare index positions become -- t' (t with the cut in place,
      without schematic variables, past the guard) under Declare; under Inherit, the cut where
      there is one*)
    val imports_state' =
      Locale.map_structure_state (fn (i, t_src) => Morphism.term (#2 (nth deps i)) t_src)
        imports_state;
    fun place_cut x =
      (case imports_state' of Locale.Structure_Of cut => map_free x (K cut) | _ => I);
    val (state, slot, place) =
      (case structure_spec of
        Syntax_Trans.Declare _ =>
          let
            val t' = Sign.no_vars ctxt5 (place_cut decl_ (the_single structures));
            val _ =
              (case Locale.light_structure_guard_of thy of
                SOME guard => guard ctxt5 {params = parms, declared = t'}
              | NONE => ());
          in (Locale.Structure_Of t', Syntax_Trans.Declare t', map_elems (map_placeholder (K t'))) end
      | Syntax_Trans.Cancel => (Locale.Cancelled_Structure, Syntax_Trans.Cancel, I)
      | Syntax_Trans.Inherit =>
          (imports_state', Syntax_Trans.Inherit,
            map_elems (place_cut Syntax_Trans.implicit_structure_)));
    val elems'' = map (finish_elem (ctxt1, ctxt5) parms do_close) (place elems');

  in ((fixed, deps, eqnss', elems'', concl, kindss, {state = state, slot = slot}), (parms, ctxt5)) end;

in

fun cert_full_context_statement x =
  prep_full_context_statement (K I) (K I) (K I) Obtain.cert_obtains
    Proof_Context.cert_var make_inst Syntax.check_props (K I) Proof_Context.cert_var (K I) x;

fun cert_read_full_context_statement x =
  prep_full_context_statement Syntax.parse_typ Syntax.parse_prop Syntax.parse_term
    Obtain.parse_obtains
    Proof_Context.read_var make_inst Syntax.check_props (K I) Proof_Context.cert_var (K I) x;

fun read_full_context_statement x =
  prep_full_context_statement Syntax.parse_typ Syntax.parse_prop Syntax.parse_term
    Obtain.parse_obtains
    Proof_Context.read_var parse_inst Syntax.read_props Attrib.check_src Proof_Context.read_var check_expr x;

end;


(* Context statement: elements + statement *)

local

fun prep_statement prep activate raw_elems raw_stmt ctxt =
  let
    val ((_, _, _, elems, concl, _, _), _) =
      prep {strict = true, do_close = false, fixed_frees = true, light = false}
        ([], []) Syntax_Trans.Inherit I raw_elems raw_stmt ctxt;
    val ctxt' = ctxt
      |> Proof_Context.set_stmt true
      |> fold_map activate elems |> #2
      |> Proof_Context.restore_stmt ctxt;
  in (concl, ctxt') end;

in

fun cert_statement x = prep_statement cert_full_context_statement Element.activate_i x;
fun read_statement x = prep_statement read_full_context_statement Element.activate x;

end;


(* Locale declaration: import + elements *)

fun fix_params params =
  Proof_Context.add_fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params) #> snd;

local

(*the locale declarations also return the position kinds of the header (plan section 3.2 item 2)
  and the slot value, for the registration*)
fun prep_locale_declaration prep activate {light} raw_import structure_spec init_body raw_elems
    ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ((fixed, deps, eqnss, elems, _, kindss, {state, slot}), (parms, ctxt0)) =
      prep {strict = false, do_close = true, fixed_frees = false, light = light}
        raw_import structure_spec init_body raw_elems (Element.Shows []) ctxt;
    val _ = null (flat eqnss) orelse error "Illegal rewrites clause(s) in declaration of locale";
    (* Declare parameters and imported facts; a light header activates its heavy imports
       syntax-only (plan decision 10); then, as in Locale.init, the header's structure state,
       which the elements' attributes read like the body (plan section 3.2 item 3) *)
    val ctxt' = ctxt
      |> fix_params fixed
      |> (if light then
            fold (fn dep => Context.proof_map (Locale.activate_facts_level
              (if Locale.is_light thy (#1 dep) then Locale.Full else Locale.Syntax_only) NONE dep)) deps
          else fold (Context.proof_map o Locale.activate_facts NONE) deps)
      |> Locale.install_structure_state (the o AList.lookup (op =) parms) state;
    val (elems', ctxt'') = ctxt'
      |> Proof_Context.set_stmt true
      |> fold_map activate elems
      ||> Proof_Context.restore_stmt ctxt';
  in (((fixed, deps, elems', ctxt''), (parms, ctxt0)), (kindss, slot)) end;

in

fun cert_locale_declaration x = prep_locale_declaration cert_full_context_statement Element.activate_i x;
fun read_locale_declaration x = prep_locale_declaration read_full_context_statement Element.activate x;

fun cert_declaration raw_import init_body raw_elems ctxt =
  #1 (cert_locale_declaration {light = false} raw_import Syntax_Trans.Inherit init_body
    raw_elems ctxt);
fun cert_read_declaration raw_import init_body raw_elems ctxt =
  #1 (prep_locale_declaration cert_read_full_context_statement Element.activate {light = false}
    raw_import Syntax_Trans.Inherit init_body raw_elems ctxt);
fun read_declaration raw_import init_body raw_elems ctxt =
  #1 (read_locale_declaration {light = false} raw_import Syntax_Trans.Inherit init_body
    raw_elems ctxt);

end;


(* Locale expression to set up a goal *)

local

fun props_of thy (name, morph) =
  let val (asm, defs) = Locale.specification_of thy name
  in map (Morphism.term morph) (the_list asm @ defs) end;

fun prep_goal_expression prep expression ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    val ((fixed, deps, eqnss, _, _, _, _), _) =
      prep {strict = true, do_close = true, fixed_frees = true, light = false} expression
        Syntax_Trans.Inherit I []
        (Element.Shows []) ctxt;
    (* proof obligations *)
    val propss = map (props_of thy) deps;
    val eq_propss = (map o map) snd eqnss;

    val goal_ctxt = ctxt
      |> fix_params fixed
      |> (fold o fold) Proof_Context.augment (propss @ eq_propss);

    val export = Proof_Context.export_morphism goal_ctxt ctxt;
    val exp_fact = Drule.zero_var_indexes_list o map Thm.strip_shyps o Morphism.fact export;
    val exp_term = Term_Subst.zero_var_indexes o Morphism.term export;
    val exp_typ = Logic.type_map exp_term;
    val export' =
      Morphism.morphism "Expression.prep_goal"
        {binding = [], typ = [K exp_typ], term = [K exp_term], fact = [K exp_fact]};
  in ((propss, eq_propss, deps, eqnss, export'), goal_ctxt) end;

in

fun cert_goal_expression x = prep_goal_expression cert_full_context_statement x;
fun read_goal_expression x = prep_goal_expression read_full_context_statement x;

end;


(*** Locale declarations ***)

(* extract specification text *)

fun bind_def ctxt eq (env, eqs) =
  let
    val _ = Local_Defs.cert_def ctxt (K []) eq;
    val ((y, T), b) = Local_Defs.abs_def eq;
    val b' = norm_term env b;
    fun err msg = error (msg ^ ": " ^ quote y);
  in
    (case filter (fn (Free (y', _), _) => y = y' | _ => false) env of
      [] => ((Free (y, T), b') :: env, eq :: eqs)
    | dups =>
        if forall (fn (_, b'') => b' aconv b'') dups then (env, eqs)
        else err "Attempt to redefine variable")
  end;

(* text has the following structure:
       (((exts, exts'), (ints, ints')), (xs, env, defs))
   where
     exts: external assumptions (terms in assumes elements)
     exts': dito, normalised wrt. env
     ints: internal assumptions (terms in assumptions from insts)
     ints': dito, normalised wrt. env
     xs: the free variables in exts' and ints' and rhss of definitions,
       this includes parameters except defined parameters
     env: list of term pairs encoding substitutions, where the first term
       is a free variable; substitutions represent defines elements and
       the rhs is normalised wrt. the previous env
     defs: the equations from the defines elements
   *)

fun eval_text _ _ (Fixes _) text = text
  | eval_text _ _ (Constrains _) text = text
  | eval_text _ is_ext (Assumes asms)
        (((exts, exts'), (ints, ints')), (env, defs)) =
      let
        val ts = maps (map #1 o #2) asms;
        val ts' = map (norm_term env) ts;
        val spec' =
          if is_ext then ((exts @ ts, exts' @ ts'), (ints, ints'))
          else ((exts, exts'), (ints @ ts, ints' @ ts'));
      in (spec', (env, defs)) end
  | eval_text ctxt _ (Defines defs) (spec, binds) =
      (spec, fold (bind_def ctxt o #1 o #2) defs binds)
  | eval_text _ _ (Notes _) text = text
  | eval_text _ _ (Lazy_Notes _) text = text;

(*the imports of a light locale contribute no defs: its header eliminated every defined
  parameter, so the inherited equations are reflexive after the morphism (plan decision 1);
  gen_add_locale proves them (def_witnesses)*)
fun eval_inst light ctxt (loc, morph) text =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (asm, defs) = Locale.specification_of thy loc;
    val asm' = Option.map (Morphism.term morph) asm;
    val defs' = map (Morphism.term morph) defs;
    val text' =
      text |>
       (if is_some asm then
          eval_text ctxt false (Assumes [(Binding.empty_atts, [(the asm', [])])])
        else I) |>
       (if not light andalso not (null defs) then
          eval_text ctxt false (Defines (map (fn def => (Binding.empty_atts, (def, []))) defs'))
        else I)
(* FIXME clone from locale.ML *)
  in text' end;

fun eval_elem ctxt elem text =
  eval_text ctxt true elem text;

fun eval light ctxt deps elems =
  let
    val text' = fold (eval_inst light ctxt) deps ((([], []), ([], [])), ([], []));
    val ((spec, (_, defs))) = fold (eval_elem ctxt) elems text';
  in (spec, defs) end;

(* axiomsN: name of theorem set with destruct rules for locale predicates,
     also name suffix of delta predicates and assumptions. *)

val axiomsN = "axioms";

local

(* introN: name of theorems for introduction rules of locale and
     delta predicates *)

val introN = "intro";

fun atomize_spec ctxt ts =
  let
    val t = Logic.mk_conjunction_balanced ts;
    val body = Object_Logic.atomize_term ctxt t;
    val bodyT = Term.fastype_of body;
  in
    if bodyT = propT
    then (t, propT, Thm.reflexive (Thm.cterm_of ctxt t))
    else (body, bodyT, Object_Logic.atomize ctxt (Thm.cterm_of ctxt t))
  end;

(* achieve plain syntax for locale predicates (without "PROP") *)

fun aprop_tr' n c =
  let
    val c' = Lexicon.mark_const c;
    fun tr' (_: Proof.context) T args =
      if T <> dummyT andalso length args = n
      then Syntax.const "_aprop" $ Term.list_comb (Syntax.const c', args)
      else raise Match;
  in (c', tr') end;

(* define one predicate including its intro rule and axioms
   - binding: predicate name
   - parms: locale parameters
   - defs: thms representing substitutions from defines elements
   - ts: terms representing locale assumptions (not normalised wrt. defs)
   - norm_ts: terms representing locale assumptions (normalised wrt. defs)
   - thy: the theory
*)

fun def_pred binding parms defs ts norm_ts thy =
  let
    val name = Sign.full_name thy binding;

    val thy_ctxt = Proof_Context.init_global thy;

    val (body, bodyT, body_eq) = atomize_spec thy_ctxt norm_ts;
    val env = Names.build (Names.add_free_names body);
    val xs = filter (Names.defined env o #1) parms;
    val Ts = map #2 xs;
    val type_tfrees = TFrees.build (fold TFrees.add_tfreesT Ts);
    val extra_tfrees =
      TFrees.build (TFrees.add_tfrees_unless (TFrees.defined type_tfrees) body)
      |> TFrees.keys |> map TFree;
    val predT = map Term.itselfT extra_tfrees ---> Ts ---> bodyT;

    val args = map Logic.mk_type extra_tfrees @ map Free xs;
    val head = Term.list_comb (Const (name, predT), args);
    val statement = Object_Logic.ensure_propT thy_ctxt head;

    val (pred_def, defs_thy) =
      thy
      |> bodyT = propT ? Sign.typed_print_translation [aprop_tr' (length args) name]
      |> Sign.declare_const_global ((binding, predT), NoSyn) |> snd
      |> Global_Theory.add_def (Thm.def_binding binding, Logic.mk_equals (head, body));
    val defs_ctxt = Proof_Context.init_global defs_thy |> Variable.declare_term head;

    val intro = Goal.prove_global defs_thy [] norm_ts statement
      (fn {context = ctxt, ...} =>
        rewrite_goals_tac ctxt [pred_def] THEN
        compose_tac defs_ctxt (false, body_eq RS Drule.equal_elim_rule1, 1) 1 THEN
        compose_tac defs_ctxt
          (false,
            Conjunction.intr_balanced (map (Thm.assume o Thm.cterm_of defs_ctxt) norm_ts), 0) 1);

    val conjuncts =
      (Drule.equal_elim_rule2 OF
        [body_eq, rewrite_rule defs_ctxt [pred_def] (Thm.assume (Thm.cterm_of defs_ctxt statement))])
      |> Conjunction.elim_balanced (length ts);

    val (_, axioms_ctxt) = defs_ctxt
      |> Assumption.add_assumes (maps Thm.chyps_of (defs @ conjuncts));
    val axioms = ts ~~ conjuncts |> map (fn (t, ax) =>
      Element.prove_witness axioms_ctxt t
       (rewrite_goals_tac axioms_ctxt defs THEN compose_tac axioms_ctxt (false, ax, 0) 1));
  in ((statement, intro, axioms), defs_thy) end;

in

(* main predicate definition function *)

fun define_preds binding parms (((exts, exts'), (ints, ints')), defs) thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val defs' = map (Thm.cterm_of ctxt #> Assumption.assume ctxt #> Drule.abs_def) defs;

    val (a_pred, a_intro, a_axioms, thy2) =
      if null exts then (NONE, NONE, [], thy)
      else
        let
          val abinding =
            if null ints then binding else Binding.suffix_name ("_" ^ axiomsN) binding;
          val ((statement, intro, axioms), thy1) =
            thy
            |> def_pred abinding parms defs' exts exts';
          val ((_, [intro']), thy2) =
            thy1
            |> Sign.qualified_path true abinding
            |> Global_Theory.note_thms ""
              ((Binding.name introN, []), [([intro], [Locale.unfold_add])])
            ||> Sign.restore_naming thy1;
          in (SOME statement, SOME intro', axioms, thy2) end;
    val (b_pred, b_intro, b_axioms, thy4) =
      if null ints then (NONE, NONE, [], thy2)
      else
        let
          val ((statement, intro, axioms), thy3) =
            thy2
            |> def_pred binding parms defs' (ints @ the_list a_pred) (ints' @ the_list a_pred);
          val conclude_witness =
            Drule.export_without_context o Element.conclude_witness (Proof_Context.init_global thy3);
          val ([(_, [intro']), _], thy4) =
            thy3
            |> Sign.qualified_path true binding
            |> Global_Theory.note_thmss ""
                 [((Binding.name introN, []), [([intro], [Locale.intro_add])]),
                  ((Binding.name axiomsN, []),
                    [(map conclude_witness axioms, [])])]
            ||> Sign.restore_naming thy3;
        in (SOME statement, SOME intro', axioms, thy4) end;
  in ((a_pred, a_intro, a_axioms), (b_pred, b_intro, b_axioms), thy4) end;

end;


(** The definitions a light header unfolds (plan decision 1, D20) **)

(*name, source locale, the value at the eliminated position, from the header edges in header
  order; the first occurrence of a name wins (plan section 3.2 item 1)*)
fun unfolded_definitions ctxt name =
  let val thy = Proof_Context.theory_of ctxt in
    build (Locale.header_edges thy name |> fold (fn (l, m, kinds) =>
      fold2 (fn ((n, T), _) => fn kind =>
          kind = Locale.Eliminated ? cons (n, (l, Morphism.term m (Free (n, T)))))
        (Locale.params_of thy l) kinds))
    |> rev |> distinct (eq_fst (op =))
  end;

(*the unfolded names the locale does not bind again*)
fun not_bound thy name unfolded =
  filter_out (member (op =) (map (#1 o #1) (Locale.params_of thy name)) o #1) unfolded;

(*the declaration warning (the unfolded definitions by source locale, then the names not bound),
  then one rebinding warning for each parameter the locale declares itself that an import
  eliminated; one string per warning; ctxt is the context the declaration leaves*)
fun unfolded_definitions_message ctxt name =
  (case unfolded_definitions ctxt name of
    [] => []
  | unfolded =>
      let
        val thy = Proof_Context.theory_of ctxt;
        fun def_line (n, (_, v)) =
          "  " ^ Syntax.string_of_term ctxt (Logic.mk_equals (Free (n, Term.fastype_of v), v));
        val blocks = distinct (op =) (map (#1 o #2) unfolded) |> maps (fn l =>
          ("The following definitions from `" ^ Locale.extern ctxt l ^ "` are unfolded.") ::
            map def_line (filter (fn (_, (l', _)) => l' = l) unfolded));
        val last =
          (case not_bound thy name unfolded of
            [] => []
          | names =>
              ["The names " ^ commas (map (fn (n, _) => "`" ^ n ^ "`") names) ^
                " are not bound and shouldn't be used any more. Write their unfolded terms instead."]);
        val sentences = Locale.own_params thy name |> map_filter (fn ((x, _), _) =>
          AList.lookup (op =) unfolded x
          |> Option.map (fn (l, _) => Locale.eliminated_name_message ctxt (x, l)));
      in cat_lines (blocks @ last) :: sentences end);


local

fun assumes_to_notes (Assumes asms) axms =
      fold_map (fn (a, spec) => fn axs =>
          let val (ps, qs) = chop (length spec) axs
          in ((a, [(ps, [])]), qs) end) asms axms
      |> apfst (curry Notes "")
  | assumes_to_notes e axms = (e, axms);

fun defines_to_notes ctxt (Defines defs) =
      Notes ("", map (fn (a, (def, _)) =>
        (a, [([Assumption.assume ctxt (Thm.cterm_of ctxt def)],
          [Attrib.internal \<^here> (K Locale.witness_add)])])) defs)
  | defines_to_notes _ e = e;

val is_hyp = fn Assumes _ => true | Defines _ => true | _ => false;

fun gen_add_locale prep_include prep_decl light
    binding raw_predicate_binding raw_includes raw_import raw_structure raw_body thy =
  let
    val name = Sign.full_name thy binding;
    val _ = Locale.defined thy name andalso
      error ("Duplicate definition of locale " ^ quote name);
    val _ =
      if light then
        List.app (fn Defines _ => error "A light locale does not support `defines` clauses"
          | Notes _ => error "A light locale does not support `notes` clauses"
          | _ => ()) raw_body
      else ();

    val ctxt = Proof_Context.init_global thy;

    (*a light header may not write (structure) parameters (header plan section 2 item 8), checked
      before anything is read*)
    val own_structures = header_structure_names raw_import raw_body;
    val _ =
      if light andalso not (null own_structures) then
        (case Locale.light_own_structure_check_of thy of
          SOME check => check ctxt own_structures
        | NONE => ())
      else ();

    val includes = map (prep_include ctxt) raw_includes;

    val (((fixed, deps, body_elems, _), (parms, ctxt')), (kindss, slot)) =
      ctxt
      |> Bundle.includes includes
      |> prep_decl {light = light} raw_import raw_structure I raw_body;
    val text as (((_, exts'), _), defs) = eval light ctxt' deps body_elems;

    val type_tfrees = TFrees.build (fold (TFrees.add_tfreesT o #2) parms);
    val extra_tfrees =
      TFrees.build (fold (TFrees.add_tfrees_unless (TFrees.defined type_tfrees)) exts')
      |> TFrees.keys;
    val _ =
      if null extra_tfrees then ()
      else warning ("Additional type variable(s) in locale specification " ^
          Binding.print binding ^ ": " ^
          commas (map (Syntax.string_of_typ ctxt' o TFree) extra_tfrees));

    val predicate_binding =
      if Binding.is_empty raw_predicate_binding then binding
      else raw_predicate_binding;
    val ((a_statement, a_intro, a_axioms), (b_statement, b_intro, b_axioms), thy') =
      define_preds predicate_binding parms text thy;
    val pred_ctxt = Proof_Context.init_global thy';

    val a_satisfy = Element.satisfy_morphism a_axioms;
    (*a light header drops its imports' defs (eval_inst); under the edge morphisms they are
      reflexive, and their witnesses discharge the definition hyps, like the defs of props_of*)
    fun def_witnesses (l, morph) =
      #2 (Locale.specification_of thy' l) |> map (fn def =>
        Element.prove_witness pred_ctxt (Morphism.term morph def)
          (resolve_tac pred_ctxt [Drule.reflexive_thm] 1));
    val b_satisfy =
      Element.satisfy_morphism (if light then b_axioms @ maps def_witnesses deps else b_axioms);

    val params = fixed @
      maps (fn Fixes fixes =>
        map (fn (b, SOME T, mx) => ((Binding.name_of b, T), mx)) fixes | _ => []) body_elems;
    val asm = if is_some b_statement then b_statement else a_statement;

    val hyp_spec = filter is_hyp body_elems;

    val notes =
      if is_some asm then
        [("", [((Binding.suffix_name ("_" ^ axiomsN) binding, []),
          [([Assumption.assume pred_ctxt (Thm.cterm_of pred_ctxt (the asm))],
            Attrib.internal \<^here> (K Locale.witness_add) ::
              (if light then
                Attrib.internal \<^here> (K Light_Locale_Axiom_Facts.add_attribute) ::
                  Locale.light_axioms_attributes_of thy
               else []))])])]
      else [];

    val notes' =
      body_elems
      |> map (Element.transfer_ctxt thy')
      |> map (defines_to_notes pred_ctxt)
      |> map (Element.transform_ctxt a_satisfy)
      |> (fn elems =>
        fold_map assumes_to_notes elems (map (Element.conclude_witness pred_ctxt) a_axioms))
      |> fst
      |> map (Element.transform_ctxt b_satisfy)
      |> map_filter (fn Notes notes => SOME notes | _ => NONE);

    val deps' = map2 (fn (l, morph) => fn kinds => (l, morph $> b_satisfy, kinds)) deps kindss;
    val axioms = map (Element.conclude_witness pred_ctxt) b_axioms;

    (*the names the header unfolds and does not bind again join the eliminated names (plan
      decision 1, D20); the warnings are printed in the context the declaration leaves*)
    fun declare_unfolded lthy =
      let
        val names = not_bound (Proof_Context.theory_of lthy) name (unfolded_definitions lthy name);
        val lthy' = lthy |> not (null names) ?
          Local_Theory.declaration {syntax = true, pervasive = false, pos = Binding.pos_of binding}
            (Locale.eliminated_names_declaration names);
        val _ = List.app warning (unfolded_definitions_message lthy' name);
      in lthy' end;

    val loc_ctxt = thy'
      |> Locale.register_locale' light binding (extra_tfrees, params)
          (asm, rev defs) (a_intro, b_intro) axioms hyp_spec [] (rev notes) (rev deps') slot
      |> Named_Target.init includes name
      |> fold (fn (kind, facts) => Local_Theory.notes_kind kind facts #> snd) notes'
      |> declare_unfolded;

  in (name, loc_ctxt) end;

in

fun add_locale binding pb includes expr elems =
  gen_add_locale (K I) cert_locale_declaration false binding pb includes expr
    Syntax_Trans.Inherit elems;
fun add_locale_cmd binding pb includes expr elems =
  gen_add_locale Bundle.check_name read_locale_declaration false binding pb includes expr
    Syntax_Trans.Inherit elems;
val add_light_locale = gen_add_locale (K I) cert_locale_declaration true;
val add_light_locale_cmd = gen_add_locale Bundle.check_name read_locale_declaration true;

end;

end;
