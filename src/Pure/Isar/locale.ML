(*  Title:      Pure/Isar/locale.ML
    Author:     Clemens Ballarin, TU Muenchen

Locales -- managed Isar proof contexts, based on Pure predicates.

Draws basic ideas from Florian Kammueller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, structured composition of contexts (with merge
and instantiation) is provided, as well as type-inference of the
signature parts and predicate definitions of the specification text.

Interpretation enables the transfer of declarations and theorems to other
contexts, namely those defined by theories, structured proofs and locales
themselves.

A comprehensive account of locales is available:

[1] Clemens Ballarin. Locales: a module system for mathematical theories.
    Journal of Automated Reasoning, 52(2):123-153, 2014.

See also:

[2] Clemens Ballarin. Locales and Locale Expressions in Isabelle/Isar.
    In Stefano Berardi et al., Types for Proofs and Programs: International
    Workshop, TYPES 2003, Torino, Italy, LNCS 3085, pages 34-50, 2004.
[3] Clemens Ballarin. Interpretation of Locales in Isabelle: Managing
    Dependencies between Locales. Technical Report TUM-I0607, Technische
    Universitaet Muenchen, 2006.
[4] Clemens Ballarin. Interpretation of Locales in Isabelle: Theories and
    Proof Contexts. In J.M. Borwein and W.M. Farmer, MKM 2006, LNAI 4108,
    pages 31-43, 2006.
*)

signature LOCALE =
sig
  (* Light locales: activation levels and header position kinds *)
  datatype level = Syntax_only | Full
  datatype position_kind = Written | Inherited | Eliminated

  (* Locale specification *)
  val register_locale: binding ->
    (string * sort) list * ((string * typ) * mixfix) list ->
    term option * term list ->
    thm option * thm option -> thm list ->
    Element.context_i list ->
    Morphism.declaration_entity list ->
    (string * Attrib.fact list) list ->
    (string * morphism) list -> theory -> theory
  val register_locale': bool -> binding ->
    (string * sort) list * ((string * typ) * mixfix) list ->
    term option * term list ->
    thm option * thm option -> thm list ->
    Element.context_i list ->
    Morphism.declaration_entity list ->
    (string * Attrib.fact list) list ->
    (string * morphism * position_kind list) list -> term Syntax_Trans.implicit_structure_spec ->
    theory -> theory
  val is_light: theory -> string -> bool
  val is_light_predicate: theory -> string -> bool
  datatype 'a structure_state =
    Inherited_Structure | Cancelled_Structure | Structure_Of of 'a | Structure_Head of string
  val map_structure_state: ('a -> 'b) -> 'a structure_state -> 'b structure_state
  val imports_structure_state: theory -> string list -> (string * position_kind list) list ->
    (int * term) structure_state
  val install_structure_state: (string -> typ) -> term structure_state ->
    Proof.context -> Proof.context
  val parent_implicit_structures: theory -> string -> (string * term option) list
  val locale_space: theory -> Name_Space.T
  val intern: theory -> xstring -> string
  val check_global: theory -> xstring * Position.T -> string
  val check: Proof.context -> xstring * Position.T -> string
  val extern: Proof.context -> string -> xstring
  val markup_name: Proof.context -> string -> string
  val pretty_name: Proof.context -> string -> Pretty.T
  val defined: theory -> string -> bool
  val parameters_of: theory -> string -> (string * sort) list * ((string * typ) * mixfix) list
  val params_of: theory -> string -> ((string * typ) * mixfix) list
  val intros_of: theory -> string -> thm option * thm option
  val axioms_of: theory -> string -> thm list
  val instance_of: theory -> string -> morphism -> term list
  val specification_of: theory -> string -> term option * term list
  val hyp_spec_of: theory -> string -> Element.context_i list

  (* Storing results *)
  val add_facts: string -> string -> Attrib.fact list -> Proof.context -> Proof.context
  val add_declaration: string -> {syntax: bool, pos: Position.T} ->
    Morphism.declaration_entity -> Proof.context -> Proof.context

  (* Activation *)
  val activate_facts: morphism option -> string * morphism -> Context.generic -> Context.generic
  val activate_facts_level: level -> morphism option -> string * morphism ->
    Context.generic -> Context.generic
  val activate_declarations: string * morphism -> Proof.context -> Proof.context
  val init: string -> theory -> Proof.context
  val matching_marks_of: Context.generic -> string * term list ->
    (term list * level * string list) list

  (* Light locale hooks and eliminated names *)
  val set_light_axioms_attributes: Token.src list -> theory -> theory
  val light_axioms_attributes_of: theory -> Token.src list
  val set_light_degeneracy_check: (string -> Attrib.fact list -> local_theory -> unit) ->
    theory -> theory
  val light_degeneracy_check_of: theory ->
    (string -> Attrib.fact list -> local_theory -> unit) option
  val set_light_own_structure_check: (Proof.context -> string list -> unit) -> theory -> theory
  val light_own_structure_check_of: theory -> (Proof.context -> string list -> unit) option
  val set_light_structure_guard:
    (Proof.context -> {params: (string * typ) list, declared: term} -> unit) -> theory -> theory
  val light_structure_guard_of: theory ->
    (Proof.context -> {params: (string * typ) list, declared: term} -> unit) option
  val eliminated_names_of: Proof.context -> (string * term) Symtab.table
  val eliminated_names_declaration: (string * (string * term)) list -> Morphism.declaration
  val eliminated_name_message: Proof.context -> string * string -> string
  val eliminated_name_warning: Proof.context -> string * string -> unit
  val header_edges: theory -> string -> (string * morphism * position_kind list) list
  val own_params: theory -> string -> ((string * typ) * mixfix) list

  (* Reasoning about locales *)
  val get_witnesses: Proof.context -> thm list
  val get_intros: Proof.context -> thm list
  val get_unfolds: Proof.context -> thm list
  val witness_add: attribute
  val intro_add: attribute
  val unfold_add: attribute
  val intro_locales_tac: {strict: bool, eager: bool} -> Proof.context -> thm list -> tactic

  (* Registrations and dependencies *)
  type registration = {inst: string * morphism, mixin: (morphism * bool) option, export: morphism}
  val amend_registration: registration -> Context.generic -> Context.generic
  val add_registration: registration -> Context.generic -> Context.generic
  val add_registration_level: level -> registration -> Context.generic -> Context.generic
  val registrations_of: Context.generic -> string -> (string * morphism) list
  val add_dependency: string -> registration -> theory -> theory

  (* Diagnostic *)
  val get_locales: theory -> string list
  val locale_notes: theory -> string -> (string * Attrib.fact list) list
  val pretty_locales: theory -> bool -> Pretty.T
  val pretty_locale: theory -> bool -> string -> Pretty.T
  val pretty_registrations: Proof.context -> string -> Pretty.T
  val pretty_locale_deps: theory -> {name: string, parents: string list, body: Pretty.T} list
  type locale_dependency =
    {source: string, target: string, prefix: (string * bool) list, morphism: morphism,
      pos: Position.T, serial: serial}
  val dest_dependencies: theory list -> theory -> locale_dependency list
  val tracing : Proof.context -> string -> unit
end;

structure Locale: LOCALE =
struct

datatype ctxt = datatype Element.ctxt;


(*** Locales ***)

(* light locales (plan decisions 2-7, 16): activation level of an arrival, header position
   kinds, note tags, marks of activated instances, note selection and roundup client kinds *)

datatype level = Syntax_only | Full;
datatype position_kind = Written | Inherited | Eliminated;
datatype note_tag = Plain | Syntax_copy | Axiom;
datatype mark = Full_mark | Syntax_only_mark of string list;  (*named effects served*)
datatype selection = All | Light | Rest;
(*a roundup client carries its callback, which receives only what that kind consumes*)
datatype 'a client =
  Installs_notes of selection -> string * morphism -> 'a -> 'a |
  Declarations_only of string * morphism -> 'a -> 'a |
  Collects_only of level -> string * morphism -> 'a -> 'a;

fun level_of Full_mark = Full
  | level_of (Syntax_only_mark _) = Syntax_only;

fun effects_of Full_mark = []
  | effects_of (Syntax_only_mark effs) = effs;

(*recorded level satisfies the requested one*)
fun satisfies requested recorded = not (requested = Full andalso recorded = Syntax_only);

fun syntax_only_tag Plain = false
  | syntax_only_tag Syntax_copy = true
  | syntax_only_tag Axiom = true;

(*the named effect of an activation chain on fact names*)
fun named_effect morph = Binding.long_name_of (Morphism.binding morph (Binding.name "x"));

type dep =
 {name: string, morphisms: morphism * morphism, header: position_kind list option,
  pos: Position.T, serial: serial};
fun eq_dep (dep1: dep, dep2: dep) = #serial dep1 = #serial dep2;

fun transfer_dep thy ({name, morphisms, header, pos, serial}: dep) : dep =
  {name = name, morphisms = apply2 (Morphism.set_context thy) morphisms, header = header,
    pos = pos, serial = serial};

fun make_dep (name, morphisms) header : dep =
 {name = name,
  morphisms = apply2 Morphism.reset_context morphisms,
  header = header,
  pos = Position.thread_data (),
  serial = serial ()};

(*table of mixin lists, per list mixins in reverse order of declaration;
  lists indexed by registration/dependency serial,
  entries for empty lists may be omitted*)
type mixin = (morphism * bool) * serial;
type mixins = mixin list Inttab.table;

fun lookup_mixins (mixins: mixins) serial' = Inttab.lookup_list mixins serial';

val merge_mixins: mixins * mixins -> mixins = Inttab.merge_list (eq_snd op =);

fun insert_mixin serial' (morph, b) : mixins -> mixins =
  Inttab.cons_list (serial', ((Morphism.reset_context morph, b), serial ()));

fun rename_mixin (old, new) (mixins: mixins) =
  (case Inttab.lookup mixins old of
    NONE => mixins
  | SOME mixin => Inttab.delete old mixins |> Inttab.update_new (new, mixin));

fun compose_mixins (mixins: mixin list) =
  fold_rev Morphism.compose (map (fst o fst) mixins) Morphism.identity;

datatype locale = Loc of {
  (* static part *)

  (*type and term parameters*)
  parameters: (string * sort) list * ((string * typ) * mixfix) list,
  (*assumptions (as a single predicate expression) and defines*)
  spec: term option * term list,
  intros: thm option * thm option,
  axioms: thm list,
  (*diagnostic device: theorem part of hypothetical body as specified by the user*)
  hyp_spec: Element.context_i list,
  (*declared by light_locale*)
  light: bool,
  (*the implicit structure element of the header (header plan section 3.5): inherited, cancelled
    or declared; written at registration only*)
  implicit_structure: term Syntax_Trans.implicit_structure_spec,

  (* dynamic part *)

  (*syntax declarations*)
  syntax_decls: (Morphism.declaration_entity * serial) list,
  (*theorem declarations, tagged for syntax-only activation*)
  notes: ((string * Attrib.fact list) * serial * note_tag) list,
  (*locale dependencies (sublocale relation) in reverse order*)
  dependencies: dep list,
  (*mixin part of dependencies*)
  mixins: mixins
};

fun mk_locale ((parameters, spec, intros, axioms, hyp_spec, light, implicit_structure),
    ((syntax_decls, notes), (dependencies, mixins))) =
  Loc {parameters = parameters, spec = spec, intros = intros, axioms = axioms, hyp_spec = hyp_spec,
    light = light, implicit_structure = implicit_structure, syntax_decls = syntax_decls,
    notes = notes, dependencies = dependencies, mixins = mixins};

fun map_locale f (Loc {parameters, spec, intros, axioms, hyp_spec, light, implicit_structure,
    syntax_decls, notes, dependencies, mixins}) =
  mk_locale (f ((parameters, spec, intros, axioms, hyp_spec, light, implicit_structure),
    ((syntax_decls, notes), (dependencies, mixins))));

val eq_note = op = o apply2 #2;

fun merge_locale
 (Loc {parameters, spec, intros, axioms, hyp_spec, light, implicit_structure, syntax_decls, notes,
    dependencies, mixins},
  Loc {syntax_decls = syntax_decls', notes = notes',
      dependencies = dependencies', mixins = mixins', ...}) =
    mk_locale
      ((parameters, spec, intros, axioms, hyp_spec, light, implicit_structure),
        ((merge (eq_snd op =) (syntax_decls, syntax_decls'),
          merge eq_note (notes, notes')),
            (merge eq_dep (dependencies, dependencies'),
              (merge_mixins (mixins, mixins')))));

structure Locales = Theory_Data
(
  type T = locale Name_Space.table;
  val empty : T = Name_Space.empty_table Markup.localeN;
  val merge = Name_Space.join_tables (K merge_locale);
);

val locale_space = Name_Space.space_of_table o Locales.get;
val intern = Name_Space.intern o locale_space;

fun check_global thy =
  #1 o Name_Space.check (Context.Theory thy) (Locales.get thy);

fun check ctxt =
  #1 o Name_Space.check (Context.Proof ctxt) (Locales.get (Proof_Context.theory_of ctxt));

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>locale\<close>
   (Args.context -- Scan.lift Parse.embedded_position >>
      (ML_Syntax.print_string o uncurry check)));

fun extern ctxt =
  Name_Space.extern ctxt (locale_space (Proof_Context.theory_of ctxt));

fun markup_extern ctxt =
  Name_Space.markup_extern ctxt (locale_space (Proof_Context.theory_of ctxt));

fun markup_name ctxt name = markup_extern ctxt name |-> Markup.markup;
fun pretty_name ctxt name = markup_extern ctxt name |> Pretty.mark_str;

val get_locale = Name_Space.lookup o Locales.get;
val defined = is_some oo get_locale;

fun the_locale thy name =
  (case get_locale thy name of
    SOME (Loc loc) => loc
  | NONE => error ("Unknown locale " ^ quote name));

fun register_locale_tagged tag light
    binding parameters spec intros axioms hyp_spec syntax_decls notes dependencies slot thy =
  thy |> Locales.map (Name_Space.define (Context.Theory thy) true
    (binding,
      mk_locale ((parameters, spec, (apply2 o Option.map) Thm.trim_context intros,
          map Thm.trim_context axioms,
          map Element.trim_context_ctxt hyp_spec, light, slot),
        ((map (fn decl => (Morphism.entity_reset_context decl, serial ())) syntax_decls,
          map (fn (a, facts) => ((a, map Attrib.trim_context_fact facts), serial (), tag)) notes),
          (map (fn (name, morph, header) => make_dep (name, (morph, Morphism.identity)) header)
            dependencies,
            Inttab.empty)))) #> snd);
          (* FIXME Morphism.identity *)

(*the old entry point: Plain notes, heavy, no header record -- as before*)
fun register_locale binding parameters spec intros axioms hyp_spec syntax_decls notes dependencies =
  register_locale_tagged Plain false binding parameters spec intros axioms hyp_spec syntax_decls notes
    (map (fn (name, morph) => (name, morph, NONE)) dependencies) Syntax_Trans.Inherit;

(*the entry point of the locale and light_locale commands: Axiom notes, header record, the
  implicit structure slot*)
fun register_locale' light binding parameters spec intros axioms hyp_spec syntax_decls notes
    dependencies slot =
  register_locale_tagged Axiom light binding parameters spec intros axioms hyp_spec syntax_decls notes
    (map (fn (name, morph, header) => (name, morph, SOME header)) dependencies) slot;

fun change_locale name =
  Locales.map o Name_Space.map_table_entry name o map_locale o apsnd;

fun is_light thy = #light o the_locale thy;



(** Primitive operations **)

fun parameters_of thy = #parameters o the_locale thy;
val params_of = #2 oo parameters_of;

fun intros_of thy = (apply2 o Option.map) (Thm.transfer thy) o #intros o the_locale thy;

fun axioms_of thy = map (Thm.transfer thy) o #axioms o the_locale thy;

fun instance_of thy name morph = params_of thy name |>
  map (Morphism.term (Morphism.set_context thy morph) o Free o #1);

fun specification_of thy = #spec o the_locale thy;

fun hyp_spec_of thy = map (Element.transfer_ctxt thy) o #hyp_spec o the_locale thy;

fun dependencies_of thy = map (transfer_dep thy) o #dependencies o the_locale thy;

fun mixins_of thy name serial =
  lookup_mixins (#mixins (the_locale thy name)) serial
  |> (map o apfst o apfst) (Morphism.set_context thy);


(* Print instance and qualifiers *)

fun pretty_reg_inst ctxt qs (name, ts) =
  let
    fun print_qual (qual, mandatory) = qual ^ (if mandatory then "" else "?");
    fun prt_quals qs = Pretty.str (space_implode "." (map print_qual qs));
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    fun prt_term' t =
      if Config.get ctxt show_types
      then Pretty.block [prt_term t, Pretty.brk 1, Pretty.str "::",
        Pretty.brk 1, (Pretty.quote o Syntax.pretty_typ ctxt) (type_of t)]
      else prt_term t;
    fun prt_inst ts =
      Pretty.block (Pretty.breaks (pretty_name ctxt name :: map prt_term' ts));
  in
    (case qs of
      [] => prt_inst ts
    | qs => Pretty.block [prt_quals qs, Pretty.brk 1, Pretty.str ":", Pretty.brk 1, prt_inst ts])
  end;

fun pretty_reg ctxt export (name, morph) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val morph' = morph $> export;
    val qs = Morphism.binding_prefix morph';
    val ts = instance_of thy name morph';
  in pretty_reg_inst ctxt qs (name, ts) end;


(*** Identifiers: activated locales in theory or proof context ***)

(*name ~> instances with their marks; one record per instance (plan decision 5)*)
type idents = (term list * mark) list Symtab.table;

val empty_idents : idents = Symtab.empty;

val eq_instance = eq_list (op aconv);

(*Full_mark absorbs Syntax_only_mark; effect sets of Syntax_only_marks unite*)
fun merge_marks (Syntax_only_mark effs, Syntax_only_mark effs') =
      Syntax_only_mark (merge (op =) (effs, effs'))
  | merge_marks _ = Full_mark;

(*unchanged entries are returned as they are, like Library.insert*)
fun insert_mark (instance, mark) entries =
  (case AList.lookup eq_instance entries instance of
    NONE => (instance, mark) :: entries
  | SOME mark' =>
      let val mark'' = merge_marks (mark', mark) in
        if mark'' = mark' then entries
        else AList.update eq_instance (instance, mark'') entries
      end);

fun insert_idents (name, entry) : idents -> idents = Symtab.map_default (name, []) (insert_mark entry);

fun delete_ident (name, instance) : idents -> idents =
  Symtab.map_entry name (AList.delete eq_instance instance);

fun eq_entry ((instance1, mark1), (instance2, mark2)) =
  eq_instance (instance1, instance2) andalso mark1 = mark2;

(*Symtab.merge_list with the per-instance insert of plan decision 5*)
fun merge_idents (idents1, idents2) : idents =
  Symtab.join (fn _ => fn (entries1, entries2) =>
    if eq_list eq_entry (entries1, entries2) then raise Symtab.SAME
    else fold_rev insert_mark entries2 entries1)
    (idents1, idents2);

(*stock's redundant_ident scan, keeping the mark: p tests the mark before Pattern.matchess;
  scan is exists (stops at the first hit, like stock) or filter*)
fun matching_marks scan p thy idents (name, instance) =
  scan (fn (pat, mark) => p mark andalso Pattern.matchess thy (pat, instance))
    (Symtab.lookup_list idents name);

fun redundant_ident thy idents requested (name, instance) =
  matching_marks exists (satisfies requested o level_of) thy idents (name, instance);

(*the level of the record of exactly this instance (decision 3)*)
fun level_in idents (name, instance) =
  Option.map level_of (AList.lookup eq_instance (Symtab.lookup_list idents name) instance);

fun effect_served thy idents (name, instance) eff =
  matching_marks exists (fn Syntax_only_mark effs => member (op =) effs eff | Full_mark => false)
    thy idents (name, instance);

fun record_effect eff (name, instance) : idents -> idents =
  Symtab.map_entry name (AList.map_entry eq_instance instance
    (fn Syntax_only_mark effs => Syntax_only_mark (insert (op =) eff effs) | mark => mark));

structure Idents = Generic_Data
(
  type T = idents;
  val empty = empty_idents;
  val merge = merge_idents;
);

fun matching_marks_of context (name, instance) =
  matching_marks filter (K true) (Context.theory_of context) (Idents.get context) (name, instance)
  |> map (fn (inst, mark) => (inst, level_of mark, effects_of mark));


(** Resolve locale dependencies in a depth-first fashion **)

local

val roundup_bound = 120;

fun mark_of Full = Full_mark
  | mark_of Syntax_only = Syntax_only_mark [];

(*deps: emitted instances in reverse activation order; marked: this traversal's marks;
  first: the morphism each instance was first emitted with (plan decision 3)*)
fun add thy depth stem export start_level crossed_light_edge (name, morph) (deps, marked, first) =
  if depth > roundup_bound
  then error "Roundup bound exceeded (sublocale relation probably not terminating)."
  else
    let
      val instance = instance_of thy name (morph $> stem $> export);
      val level = if start_level = Full andalso not crossed_light_edge then Full else Syntax_only;
      (*no inheritance of mixins, regardless of requests by clients*)
      fun descend stem' =
        let
          val {dependencies, light, ...} = the_locale thy name;
          (*the dependency edge of name on the imported locale p is light (plan decision 2)*)
          fun light_edge p = light andalso not (is_light thy p);
        in
          fold_rev (fn dep0 =>
            let
              val dep as {morphisms = (morph', export'), ...} = transfer_dep thy dep0;
              val crossed_light_edge' = crossed_light_edge orelse light_edge (#name dep);
            in
              add thy (depth + 1) stem' export start_level crossed_light_edge'
                (#name dep, morph' $> export' $> compose_mixins (mixins_of thy name (#serial dep)))
            end) dependencies
        end;
    in
      if level = Full andalso level_in marked (name, instance) = SOME Syntax_only then
        (*upgrade: re-descend with the first emission's morphism, do not emit again*)
        let
          val stem' =
            (case AList.lookup eq_instance (Symtab.lookup_list first name) instance of
              SOME stem' => stem'
            | NONE => raise Fail "Locale.roundup: upgrade of an instance never emitted");
          val (deps', marked', first') =
            descend stem' ([], insert_idents (name, (instance, Full_mark)) marked, first);
        in (deps' @ deps, marked', first') end
      else if redundant_ident thy marked level (name, instance) then (deps, marked, first)
      else
        let
          val stem' = morph $> stem;
          val (deps', marked', first') =
            descend stem'
              ([], insert_idents (name, (instance, mark_of level)) marked,
                Symtab.cons_list (name, (instance, stem')) first);
        in ((name, stem') :: deps' @ deps, marked', first') end
    end;

in

(* Note that while identifiers always have the external (exported) view, the client's
   callback is presented with the internal view. *)

fun roundup thy start_level client export (name, morph) (marked, input) =
  let
    (* Find all dependencies including new ones (which are dependencies enriching
      existing registrations). *)
    val (dependencies, marked', _) =
      add thy 0 Morphism.identity export start_level false (name, morph)
        ([], empty_idents, Symtab.empty);
    (* Per element, in activation order: level, redundancy against marked, then by client kind:
       a note installer gets the note selection and has its effect recorded (plan decision 5),
       a collector gets the level. Fragments redundant by marked are dropped together with
       their own record. *)
    fun process (name, morph) (marked', input) =
      let
        val instance = instance_of thy name (morph $> export);
        val level =
          (case level_in marked' (name, instance) of
            SOME level => level
          | NONE => raise Fail "Locale.roundup: emitted instance without a record");
      in
        if redundant_ident thy marked level (name, instance)
        then (delete_ident (name, instance) marked', input)
        else
          (case client of
            Installs_notes activate =>
              let
                val eff = named_effect morph;
                val selection =
                  if level = Syntax_only then Light
                  else if effect_served thy marked (name, instance) eff orelse
                    effect_served thy marked' (name, instance) eff then Rest
                  else All;
              in (record_effect eff (name, instance) marked', activate selection (name, morph) input) end
          | Declarations_only activate => (marked', activate (name, morph) input)
          | Collects_only collect => (marked', collect level (name, morph) input))
      end;
    val (marked'', input') = fold_rev process dependencies (marked', input);
  in (merge_idents (marked, marked''), input') end;

end;


(*** Registrations: interpretations in theories or proof contexts ***)

val total_ident_ord = prod_ord fast_string_ord (list_ord Term_Ord.fast_term_ord);
structure Idtab = Table(type key = string * term list val ord = total_ident_ord);

type reg = {morphisms: morphism * morphism, level: level, pos: Position.T, serial: serial};
val eq_reg: reg * reg -> bool = op = o apply2 #serial;

(* FIXME consolidate with locale dependencies, consider one data slot only *)
structure Global_Registrations = Theory_Data'
(
  (*registrations, indexed by locale name and instance;
    unique registration serial points to mixin list*)
  type T = reg Idtab.table * mixins;
  val empty: T = (Idtab.empty, Inttab.empty);
  fun merge args =
    let
      val ctxt0 = Syntax.init_pretty_global (#1 (hd args));
      fun recursive_merge ((regs1, mixins1), (regs2, mixins2)) : T =
        (Idtab.merge eq_reg (regs1, regs2), merge_mixins (mixins1, mixins2))
        handle Idtab.DUP id =>
          let
            val reg1 = Idtab.lookup regs1 id |> the;
            val reg2 = Idtab.lookup regs2 id |> the;
          in
            if #level reg1 <> #level reg2 then
              (*levels differ: the Full record wins on both sides, with its own serial
                (plan decision 6)*)
              let val winner = if #level reg1 = Full then reg1 else reg2 in
                recursive_merge
                  ((Idtab.update (id, winner) regs1, mixins1),
                    (Idtab.update (id, winner) regs2, mixins2))
              end
            else
              (*distinct interpretations with same base: merge their mixins*)
              let
                val reg2' =
                 {morphisms = #morphisms reg2,
                  level = #level reg2,
                  pos = Position.thread_data (),
                  serial = #serial reg1};
                val regs2' = Idtab.update (id, reg2') regs2;
                val mixins2' = rename_mixin (#serial reg2, #serial reg1) mixins2;
                val _ =
                  warning ("Removed duplicate interpretation after retrieving its mixins" ^
                    Position.here_list [#pos reg1, #pos reg2] ^ ":\n  " ^
                    Pretty.string_of (pretty_reg_inst ctxt0 [] id));
              in recursive_merge ((regs1, mixins1), (regs2', mixins2')) end
          end;
    in Library.foldl1 recursive_merge (map #2 args) end;
);

structure Local_Registrations = Proof_Data
(
  type T = Global_Registrations.T;
  val init = Global_Registrations.get;
);

val get_registrations = Context.cases Global_Registrations.get Local_Registrations.get;

fun map_registrations f (Context.Theory thy) = Context.Theory (Global_Registrations.map f thy)
  | map_registrations f (Context.Proof ctxt) = Context.Proof (Local_Registrations.map f ctxt);


(* Primitive operations *)

fun add_reg thy export level (name, morph) =
  let
    val reg =
     {morphisms = (Morphism.reset_context morph, Morphism.reset_context export),
      level = level,
      pos = Position.thread_data (),
      serial = serial ()};
    val id = (name, instance_of thy name (morph $> export));
    (*a Full record replaces a Syntax_only one (new serial: the old mixins become unreachable);
      the same-level cases are unreachable and keep stock's DUP (plan decision 6)*)
    fun insert regs =
      (case Idtab.lookup regs id of
        NONE => Idtab.insert (K false) (id, reg) regs
      | SOME old =>
          (case (#level old, level) of
            (Syntax_only, Full) => Idtab.update (id, reg) regs
          | (Full, Syntax_only) => regs
          | _ => Idtab.insert (K false) (id, reg) regs));
  in (map_registrations o apfst) insert end;

fun add_mixin serial' mixin =
  (* registration to be amended identified by its serial id *)
  (map_registrations o apsnd) (insert_mixin serial' mixin);

val get_regs = #1 o get_registrations;

fun get_mixins context (name, morph) =
  let
    val thy = Context.theory_of context;
    val (regs, mixins) = get_registrations context;
  in
    (case Idtab.lookup regs (name, instance_of thy name morph) of
      NONE => []
    | SOME {serial, ...} => lookup_mixins mixins serial)
  end;

fun collect_mixins context (name, morph) =
  let
    val thy = Context.theory_of context;
  in
    roundup thy Full
      (Collects_only (K (fn dep => fn mixins => merge (eq_snd op =) (mixins, get_mixins context dep))))
      Morphism.identity (name, morph)
      (insert_idents (name, (instance_of thy name morph, Full_mark)) empty_idents, [])
    |> snd |> filter (snd o fst)  (* only inheritable mixins *)
    |> (fn x => merge (eq_snd op =) (x, get_mixins context (name, morph)))
    |> compose_mixins
  end;


(*** Activate context elements of locale ***)

fun activate_err msg kind (name, morph) context =
  cat_error msg ("The above error(s) occurred while activating " ^ kind ^ " of locale instance\n" ^
    (pretty_reg (Context.proof_of context) Morphism.identity (name, morph) |>
      Pretty.string_of));

fun gen_init_element export elem context =
  context
  |> Context.mapping I (Thm.unchecked_hyps #> Context_Position.not_really)
  |> Element.gen_init export elem
  |> Context.mapping I (fn ctxt =>
      let val ctxt0 = Context.proof_of context
      in ctxt |> Context_Position.restore_visible ctxt0 |> Thm.restore_hyps ctxt0 end);

val init_element = gen_init_element Assumption.assume_export;


(* Potentially lazy notes *)

fun make_notes kind = map (fn ((b, atts), facts) =>
  if null atts andalso forall (null o #2) facts
  then Lazy_Notes (kind, (b, Lazy.value (maps #1 facts)))
  else Notes (kind, [((b, atts), facts)]));

(* HOL-side hooks of light locales (plan decisions 11, 12), set once by Light_Locale.thy *)

structure Light_Hooks = Theory_Data
(
  type T =
   {attrs: Token.src list option,
    degeneracy: (string -> Attrib.fact list -> local_theory -> unit) option,
    own_structures: (Proof.context -> string list -> unit) option,
    structure_guard:
      (Proof.context -> {params: (string * typ) list, declared: term} -> unit) option};
  val empty: T = {attrs = NONE, degeneracy = NONE, own_structures = NONE, structure_guard = NONE};
  fun merge (hooks1: T, hooks2: T) : T =
   {attrs = merge_options (#attrs hooks1, #attrs hooks2),
    degeneracy = merge_options (#degeneracy hooks1, #degeneracy hooks2),
    own_structures = merge_options (#own_structures hooks1, #own_structures hooks2),
    structure_guard = merge_options (#structure_guard hooks1, #structure_guard hooks2)};
);

fun map_hooks f {attrs, degeneracy, own_structures, structure_guard} =
  let val (attrs', degeneracy', own_structures', structure_guard') =
    f (attrs, degeneracy, own_structures, structure_guard)
  in
   {attrs = attrs', degeneracy = degeneracy', own_structures = own_structures',
    structure_guard = structure_guard'}
  end;

fun set_light_axioms_attributes attrs =
  Light_Hooks.map (map_hooks (fn (_, d, o', g) => (SOME attrs, d, o', g)));
val light_axioms_attributes_of = these o #attrs o Light_Hooks.get;
fun set_light_degeneracy_check check =
  Light_Hooks.map (map_hooks (fn (a, _, o', g) => (a, SOME check, o', g)));
val light_degeneracy_check_of = #degeneracy o Light_Hooks.get;
fun set_light_own_structure_check check =
  Light_Hooks.map (map_hooks (fn (a, d, _, g) => (a, d, SOME check, g)));
val light_own_structure_check_of = #own_structures o Light_Hooks.get;
fun set_light_structure_guard guard =
  Light_Hooks.map (map_hooks (fn (a, d, o', _) => (a, d, o', SOME guard)));
val light_structure_guard_of = #structure_guard o Light_Hooks.get;


(* names eliminated by light locale headers, per proof context (plan decision 1, D20) *)

structure Eliminated_Names = Generic_Data
(
  type T = (string * term) Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.join (K #1);
);

val eliminated_names_of = Eliminated_Names.get o Context.Proof;

fun eliminated_names_declaration entries phi context =
  (case context of
    Context.Proof _ =>
      Eliminated_Names.map
        (fold (fn (x, (loc, t)) => Symtab.default (x, (loc, Morphism.term phi t))) entries) context
  | Context.Theory _ => context);

(*a name x eliminated by locale loc is written where it is not bound*)
fun eliminated_name_message ctxt (x, loc) =
  "The parameter `" ^ x ^ "` from locale `" ^ extern ctxt loc ^
    "` is not bound any more and treated as a fresh variable here.";

fun eliminated_name_warning ctxt = warning o eliminated_name_message ctxt;


fun locale_notes_tagged thy loc =
  fold (fn (notes, _, tag) => cons (notes, tag)) (#notes (the_locale thy loc)) [];

fun locale_notes thy loc = map #1 (locale_notes_tagged thy loc);

(*which notes a note selection installs (plan decisions 4, 7): Light keeps the syntax-only
  tags, appending the light axioms attributes to Axiom notes; Rest keeps their complement*)
fun lazy_notes_select selection thy loc =
  let
    val attrs = light_axioms_attributes_of thy;
    fun select ((kind, notes), tag) =
      (case selection of
        All => make_notes kind notes
      | Light =>
          if not (syntax_only_tag tag) then []
          else if tag = Axiom then make_notes kind (map (apfst (apsnd (fn atts => atts @ attrs))) notes)
          else make_notes kind notes
      | Rest => if syntax_only_tag tag then [] else make_notes kind notes);
  in maps select (locale_notes_tagged thy loc) end;

fun consolidate_notes elems =
  elems
  |> map_filter (fn Lazy_Notes (_, (_, ths)) => SOME ths | _ => NONE)
  |> Lazy.consolidate
  |> ignore;

fun force_notes (Lazy_Notes (kind, (b, ths))) = Notes (kind, [((b, []), [(Lazy.force ths, [])])])
  | force_notes elem = elem;


(* Declarations, facts and entire locale content *)

val trace_locales =
  Attrib.setup_config_bool (Binding.make ("trace_locales", \<^here>)) (K false);

fun tracing context msg =
  if Config.get context trace_locales then Output.tracing msg else ();
  
fun trace kind (name, morph) context =
  tracing (Context.proof_of context) ("Activating " ^ kind ^ " of " ^
    (pretty_reg (Context.proof_of context) Morphism.identity (name, morph) |> Pretty.string_of));

fun activate_syntax_decls (name, morph) context =
  let
    val _ = trace "syntax" (name, morph) context;
    val thy = Context.theory_of context;
    val {syntax_decls, ...} = the_locale thy name;
    val form_syntax_decl =
      Morphism.form o Morphism.transform morph o Morphism.entity_set_context thy;
  in
    fold_rev (form_syntax_decl o #1) syntax_decls context
      handle ERROR msg => activate_err msg "syntax" (name, morph) context
  end;

fun activate_notes activ_elem context export' selection (name, morph) input =
  let
    val thy = Context.theory_of context;
    val mixin =
      (case export' of
        NONE => Morphism.identity
      | SOME export => collect_mixins context (name, morph $> export) $> export);
    val morph' = Morphism.set_context thy (morph $> mixin);
    val notes' = map (Element.transform_ctxt morph') (lazy_notes_select selection thy name);
  in
    (notes', input) |-> fold (fn elem => fn res =>
      activ_elem (Element.transfer_ctxt thy elem) res)
  end handle ERROR msg => activate_err msg "facts" (name, morph) context;

fun activate_notes_trace activ_elem context export' selection (name, morph) context' =
  let
    val _ = trace "facts" (name, morph) context';
  in
    activate_notes activ_elem context export' selection (name, morph) context'
  end;

fun activate_all name thy activ_elem (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Binding.empty_atts, [(A, [])])]) | _ => I) |>
      (not (null defs) ?
        activ_elem (Defines (map (fn def => (Binding.empty_atts, (def, []))) defs)));
    val activate = activate_notes activ_elem (Context.Theory thy) NONE;
  in
    roundup thy Full (Installs_notes activate) Morphism.identity (name, Morphism.identity)
      (marked, input')
  end;


(** Public activation functions **)

fun activate_facts_level level export dep context =
  context
  |> Context_Position.set_visible_generic false
  |> pair (Idents.get context)
  |> roundup (Context.theory_of context) level
      (Installs_notes (activate_notes_trace init_element context export))
      (Morphism.default export) dep
  |-> Idents.put
  |> Context_Position.restore_visible_generic context;

val activate_facts = activate_facts_level Full;

fun activate_declarations dep = Context.proof_map (fn context =>
  context
  |> Context_Position.set_visible_generic false
  |> pair (Idents.get context)
  |> roundup (Context.theory_of context) Syntax_only (Declarations_only activate_syntax_decls)
      Morphism.identity dep
  |-> Idents.put
  |> Context_Position.restore_visible_generic context);

(* implicit structure of a locale (plan decision 16 (c), section 3.1 item 5) *)

(*the header edges in header order: the import, the morphism, the kind of every position*)
fun header_edges thy name =
  dependencies_of thy name
  |> map_filter (fn ({name, morphisms = (m, e), header, ...}: dep) =>
      Option.map (fn kinds => (name, m $> e, kinds)) header)
  |> rev;

fun structure_names params =
  map_filter (fn ((x, _), Mixfix.Structure _) => SOME x | _ => NONE) params;

(*the parameters a locale declares itself (its header's for clause and fixes elements): not the
  image of an inherited position of a header edge*)
fun own_params thy name =
  let
    val inherited =
      header_edges thy name |> maps (fn (l, _, kinds) =>
        map_filter (fn (((x, _), _), Inherited) => SOME x | _ => NONE)
          (params_of thy l ~~ kinds));
  in filter_out (member (op =) inherited o #1 o #1) (params_of thy name) end;

fun own_structure_params thy name = structure_names (own_params thy name);

(*the summary of a locale: the surviving (structure) names in order of first occurrence, the
  cut -- the first eliminated (structure) position of a header edge, or an import's own cut --
  in the locale's own vocabulary, and whether a cancelled slot is reachable through the header
  edges; its slot overrides everything.  imports_summary walks the imports of a header and
  reports the cut untransported: the import's index and the term in the import's vocabulary.
  Where no cancelled slot is reachable the summary is the one of a world without cancellation;
  where one is reachable and no cut is found, the surviving names are the imports' followed by
  the locale's own (structure) parameters.  The memo table carries the summaries of the locales
  visited.*)
fun imports_summary thy imports memo =
  let
    val (summaries, memo') = fold_map (structure_summary thy o fst) imports memo;
    fun scan_block (i, ((loc, kinds), ((ns, cut_loc), _))) names =
      let
        val params = params_of thy loc;
        fun position n = find_index (fn ((x, _), _) => x = n) params;
        fun walk [] names = (names, NONE)
          | walk (n :: ns) names =
              (case nth kinds (position n) of
                Written => walk ns names
              | Inherited => walk ns (if member (op =) names n then names else names @ [n])
              | Eliminated => (names, SOME (Free (#1 (nth params (position n))))));
        val (names', cut) = walk ns names;
      in (names', Option.map (pair i) (if is_some cut then cut else cut_loc)) end;
    fun scan [] names = (names, NONE)
      | scan (block :: blocks) names =
          (case scan_block block names of
            (names', NONE) => scan blocks names'
          | result => result);
  in ((scan (map_index I (imports ~~ summaries)) [], exists snd summaries), memo') end
and structure_summary thy name memo =
  (case Symtab.lookup memo name of
    SOME summary => (summary, memo)
  | NONE =>
      let
        val (summary, memo') =
          (case #implicit_structure (the_locale thy name) of
            Syntax_Trans.Declare t => ((([], SOME t), false), memo)
          | Syntax_Trans.Cancel => ((([], NONE), true), memo)
          | Syntax_Trans.Inherit =>
              let
                val edges = header_edges thy name;
                val (((names, cut), reachable), memo') =
                  imports_summary thy (map (fn (l, _, kinds) => (l, kinds)) edges) memo;
                val summary =
                  (case cut of
                    SOME (i, t_src) => (names, SOME (Morphism.term (#2 (nth edges i)) t_src))
                  | NONE =>
                      if reachable then (names @ own_structure_params thy name, NONE)
                      else (structure_names (params_of thy name), NONE));
              in ((summary, reachable), memo') end);
      in (summary, Symtab.update (name, summary) memo') end);

(*a cut counts only while no (structure) name survives before it*)
fun project (names, cut) = if null names then cut else NONE;

(*how a bare index position reads in a context with this summary: the cut where one counts;
  else, where a cancelled slot is reachable, the first surviving variable structure expressed
  through the implicit structure, so that a cancelled parent's structure does not read, and
  cancelled where none survives and no cut counts; elsewhere nothing changes*)
datatype 'a structure_state =
  Inherited_Structure | Cancelled_Structure | Structure_Of of 'a | Structure_Head of string;

fun structure_state ((names, cut), reachable) =
  (case project (names, cut) of
    SOME t => Structure_Of t
  | NONE =>
      if not reachable then Inherited_Structure
      else (case names of [] => Cancelled_Structure | h :: _ => Structure_Head h));

fun map_structure_state f (Structure_Of x) = Structure_Of (f x)
  | map_structure_state _ Inherited_Structure = Inherited_Structure
  | map_structure_state _ Cancelled_Structure = Cancelled_Structure
  | map_structure_state _ (Structure_Head h) = Structure_Head h;

fun locale_structure_state thy name =
  structure_state (#1 (structure_summary thy name Symtab.empty));

(*the state a header gives its body, in the imports' vocabulary: the imports' summary, completed
  as structure_summary completes a locale's with the (structure) parameters the header writes
  itself*)
fun imports_structure_state thy own imports =
  let val ((names, cut), reachable) = #1 (imports_summary thy imports Symtab.empty)
  in structure_state ((if is_none cut then names @ own else names, cut), reachable) end;

fun install_structure_state typ_of state ctxt =
  (case state of
    Structure_Of t => Proof_Context.declare_implicit_structure t ctxt
  | Structure_Head h => Proof_Context.declare_implicit_structure (Free (h, typ_of h)) ctxt
  | Cancelled_Structure => Syntax_Trans.put_implicit_structure Syntax_Trans.Cancel ctxt
  | Inherited_Structure => ctxt);

fun param_type thy name x = the (AList.lookup (op =) (map #1 (params_of thy name)) x);

(*one entry per header edge: the import and how a bare index position reads in it, under the
  edge's morphism; inherited reads the import's first variable structure, none when there is none*)
fun parent_implicit_structures thy name =
  header_edges thy name |> map (fn (l, morph, _) =>
    let
      fun var x = SOME (Morphism.term morph (Free (x, param_type thy l x)));
      val reading =
        (case locale_structure_state thy l of
          Structure_Of t => SOME (Morphism.term morph t)
        | Structure_Head h => var h
        | Cancelled_Structure => NONE
        | Inherited_Structure =>
            (case structure_names (params_of thy l) of h :: _ => var h | [] => NONE));
    in (l, reading) end);

(*the light locale's own assumption: pasted as by assume_export (a goal too, as in a heavy
  locale); its premises are setclass premises, K grows by their number (head of setclass.ML)*)
fun setclass_export is_goal asms =
  let val (exp, term_exp) = Assumption.assume_export is_goal asms
  in (fn th => Setclass.put (Setclass.count_of th + length asms) (exp th), term_exp) end;

fun init name thy =
  let
    val context = Context.Proof (Proof_Context.init_global thy);
    val marked = Idents.get context;
    val export = if is_light thy name then setclass_export else Assumption.assume_export;
  in
    context
    |> Context_Position.set_visible_generic false
    |> pair empty_idents
    |> activate_all name thy (gen_init_element export)
    |-> (fn marked' => Idents.put (merge_idents (marked, marked')))
    |> Context_Position.restore_visible_generic context
    |> Context.proof_of
    |> install_structure_state (param_type thy name) (locale_structure_state thy name)
  end;


(*** Add and extend registrations ***)

type registration = Locale.registration;

fun amend_registration {mixin = NONE, ...} context = context
  | amend_registration {inst = (name, morph), mixin = SOME mixin, export} context =
      let
        val thy = Context.theory_of context;
        val ctxt = Context.proof_of context;

        val regs = get_regs context;
        val base = instance_of thy name (morph $> export);
        val serial' =
          (case Idtab.lookup regs (name, base) of
            NONE =>
              error ("No interpretation of locale " ^ quote (markup_name ctxt name) ^
                " with\nparameter instantiation " ^
                implode_space (map (quote o Syntax.string_of_term_global thy) base) ^
                " available")
          | SOME {serial = serial', ...} => serial');
      in
        add_mixin serial' mixin context
      end;

(* Note that a registration that would be subsumed by an existing one will not be
   generated, and it will not be possible to amend it. *)

fun gen_add_registration level {inst = (name, base_morph), mixin, export} context =
  let
    val thy = Context.theory_of context;
    val pos_morph = Morphism.binding_morphism "position" (Binding.set_pos (Position.thread_data ()));
    val mix_morph = (case mixin of NONE => base_morph | SOME (mix, _) => base_morph $> mix);
    val inst = instance_of thy name mix_morph;
    val idents = Idents.get context;
  in
    if redundant_ident thy idents level (name, inst) then context  (* FIXME amend mixins? *)
    else
      (idents, context)
      (* add new registrations with inherited mixins *)
      |> roundup thy level (Collects_only (add_reg thy export)) export (name, mix_morph) |> #2
      (* add mixin *)
      |> amend_registration {inst = (name, mix_morph), mixin = mixin, export = export}
      (* activate import hierarchy as far as not already active *)
      |> activate_facts_level level (SOME export) (name, mix_morph $> pos_morph)
  end;

val add_registration_level = gen_add_registration;
val add_registration = gen_add_registration Full;



(*** Dependencies ***)

(*with the level and the key instance of each registration*)
fun registrations_of_level context loc =
  Idtab.fold_rev (fn ((name, instance), {morphisms, level, ...}) =>
    name = loc ? cons (level, instance, (name, morphisms))) (get_regs context) []
  (*with inherited mixins*)
  |> map (fn (level, instance, (name, (base, export))) =>
      (level, instance, (name, base $> (collect_mixins context (name, base $> export)) $> export)));

val registrations_of = map #3 oo registrations_of_level;

fun add_dependency loc {inst = (name, morph), mixin, export} thy =
  let
    val dep = make_dep (name, (morph, export)) NONE;
    val add_dep =
      apfst (cons dep) #>
      apsnd (case mixin of NONE => I | SOME mixin => insert_mixin (#serial dep) mixin);
    val thy' = change_locale loc (apsnd add_dep) thy;
    val context' = Context.Theory thy';
    (*collect from each registration at its own level; register the Full ones after the
      Syntax_only ones, fold_rev starting from the end (plan decision 6 (b))*)
    val (_, regs) =
      fold_rev (fn (level, _, inst) =>
          roundup thy' level (Collects_only (curry cons)) export inst)
        (registrations_of_level context' loc) (Idents.get context', []);
    val (full, syn) = List.partition (fn (level, _) => level = Full) regs;
  in
    fold_rev (fn (level, inst) =>
        Context.theory_map (gen_add_registration level {inst = inst, mixin = NONE, export = export}))
      (full @ syn) thy'
  end;



(*** Storing results ***)

fun add_facts_tagged tag loc kind facts ctxt =
  if null facts then ctxt
  else
    let
      val stored_notes = ((kind, map Attrib.trim_context_fact facts), serial (), tag);
      val applied_notes = make_notes kind facts;

      fun apply_notes morph = applied_notes |> fold (fn elem => fn thy =>
        let val elem' = Element.transform_ctxt (Morphism.set_context thy morph) elem
        in Context.theory_map (Element.init elem') thy end);
      (*a Syntax_only registration replays the syntax-only tags only; a Full registration
        whose named effect a Syntax_only_mark already served replays Plain only (decision 6)*)
      fun replays thy (Syntax_only, _, _) = syntax_only_tag tag
        | replays thy (Full, instance, (_, morph)) =
            not (syntax_only_tag tag) orelse
            not (effect_served thy (Idents.get (Context.Theory thy)) (loc, instance)
              (named_effect morph));
      fun apply_registrations thy =
        fold_rev (fn reg => replays thy reg ? apply_notes (#2 (#3 reg)))
          (registrations_of_level (Context.Theory thy) loc) thy;
    in
      ctxt
      |> Attrib.local_notes kind facts |> #2
      |> Proof_Context.background_theory
        ((change_locale loc o apfst o apsnd) (cons stored_notes) #> apply_registrations)
    end;

val add_facts = add_facts_tagged Plain;

fun add_declaration loc {syntax, pos} decl =
  let val decl0 = Morphism.entity_reset_context decl in
    syntax ?
      Proof_Context.background_theory
        ((change_locale loc o apfst o apfst) (cons (decl0, serial ())))
    #> add_facts_tagged (if syntax then Syntax_copy else Plain) loc ""
      [(Binding.empty_atts, Attrib.internal_declaration pos decl0)]
  end;


(*** Reasoning about locales ***)

(* Storage for witnesses, intro and unfold rules *)

structure Thms = Generic_Data
(
  type T = thm Item_Net.T * thm Item_Net.T * thm Item_Net.T;
  val empty = (Thm.item_net, Thm.item_net, Thm.item_net);
  fun merge ((witnesses1, intros1, unfolds1), (witnesses2, intros2, unfolds2)) =
   (Item_Net.merge (witnesses1, witnesses2),
    Item_Net.merge (intros1, intros2),
    Item_Net.merge (unfolds1, unfolds2));
);

fun get_thms which ctxt =
  map (Thm.transfer' ctxt) (which (Thms.get (Context.Proof ctxt)));

val get_witnesses = get_thms (Item_Net.content o #1);
val get_intros = get_thms (Item_Net.content o #2);
val get_unfolds = get_thms (Item_Net.content o #3);

val witness_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (Item_Net.update (Thm.trim_context th) x, y, z)));

val intro_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (x, Item_Net.update (Thm.trim_context th) y, z)));

val unfold_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (x, y, Item_Net.update (Thm.trim_context th) z)));


(* Tactics *)

fun intro_locales_tac {strict, eager} ctxt =
  (if strict then Method.intros_tac else Method.try_intros_tac) ctxt
    (get_witnesses ctxt @ get_intros ctxt @ (if eager then get_unfolds ctxt else []));

val _ = Theory.setup
 (Method.setup \<^binding>\<open>intro_locales\<close>
    (Scan.succeed (METHOD o intro_locales_tac {strict = false, eager = false}))
    "back-chain introduction rules of locales without unfolding predicates" #>
  Method.setup \<^binding>\<open>unfold_locales\<close>
    (Scan.succeed (METHOD o intro_locales_tac {strict = false, eager = true}))
    "back-chain all introduction rules of locales");


(*** diagnostic commands and interfaces ***)

fun get_locales thy = map #1 (Name_Space.dest_table (Locales.get thy));

fun pretty_locales thy verbose =
  Pretty.block
    (Pretty.breaks
      (Pretty.str "locales:" ::
        map (Pretty.mark_str o #1)
          (Name_Space.markup_table verbose (Proof_Context.init_global thy) (Locales.get thy))));

fun pretty_locale thy show_facts name =
  let
    val locale_ctxt = init name thy;
    fun cons_elem (elem as Notes _) = show_facts ? cons elem
      | cons_elem (elem as Lazy_Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      activate_all name thy cons_elem (empty_idents, [])
      |> snd |> rev
      |> tap consolidate_notes
      |> map force_notes;
    val keyword = if is_light thy name then "light_locale" else "locale";
  in
    Pretty.block (Pretty.keyword1 keyword :: Pretty.brk 1 :: pretty_name locale_ctxt name ::
      maps (fn elem => [Pretty.fbrk, Pretty.chunks (Element.pretty_ctxt locale_ctxt elem)]) elems)
  end;

(*a light locale's own predicate, when it has assumptions (plan decision 19)*)
fun is_light_predicate thy c =
  defined thy c andalso is_light thy c andalso is_some (#1 (specification_of thy c));

fun pretty_registrations ctxt name =
  (case registrations_of (Context.Proof ctxt) name of
    [] => Pretty.str "no interpretations"
  | regs => Pretty.big_list "interpretations:" (map (pretty_reg ctxt Morphism.identity) (rev regs)));

fun pretty_locale_deps thy =
  let
    fun make_node name =
     {name = name,
      parents = map #name (dependencies_of thy name),
      body = pretty_locale thy false name};
    val names = sort_strings (Name_Space.fold_table (cons o #1) (Locales.get thy) []);
  in map make_node names end;

type locale_dependency =
  {source: string, target: string, prefix: (string * bool) list, morphism: morphism,
    pos: Position.T, serial: serial};

fun dest_dependencies prev_thys thy =
  let
    fun remove_prev loc prev_thy deps =
      (case get_locale prev_thy loc of
        NONE => deps
      | SOME (Loc {dependencies = prev_deps, ...}) =>
          if eq_list eq_dep (prev_deps, deps) then []
          else subtract eq_dep prev_deps deps);
    fun result loc (dep: dep) =
      let val morphism = op $> (#morphisms dep) in
       {source = #name dep,
        target = loc,
        prefix = Morphism.binding_prefix morphism,
        morphism = morphism,
        pos = #pos dep,
        serial = #serial dep}
      end;
    fun add (loc, Loc {dependencies = deps, ...}) =
      fold (cons o result loc) (fold (remove_prev loc) prev_thys deps);
  in
    Name_Space.fold_table add (Locales.get thy) []
    |> sort (int_ord o apply2 #serial)
  end;

end;
