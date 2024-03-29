(*  Title:      Tools/IsaPlanner/rw_inst.ML
    Author:     Lucas Dixon, University of Edinburgh

Rewriting using a conditional meta-equality theorem which supports
schematic variable instantiation.
*)

signature RW_INST =
sig
  val rw: Proof.context ->
    ((indexname * (sort * typ)) list * (* type var instantiations *)
     (indexname * (typ * term)) list) (* schematic var instantiations *)
    * (string * typ) list (* Fake named bounds + types *)
    * (string * typ) list (* names of bound + types *)
    * term -> (* outer term for instantiation *)
    thm -> (* rule with indexes lifted *)
    thm -> (* target thm *)
    thm  (* rewritten theorem possibly with additional premises for rule conditions *)
end;

structure RW_Inst: RW_INST =
struct

(* Given (string,type) pairs capturing the free vars that need to be
allified in the assumption, and a theorem with assumptions possibly
containing the free vars, then we give back the assumptions allified
as hidden hyps.

Given: x
th: A vs ==> B vs
Results in: "B vs" [!!x. A x]
*)
fun allify_conditions ctxt Ts th =
  let
    fun allify (x, T) t =
      Logic.all_const T $ Abs (x, T, Term.abstract_over (Free (x, T), t));

    val cTs = map (Thm.cterm_of ctxt o Free) Ts;
    val cterm_asms = map (Thm.cterm_of ctxt o fold_rev allify Ts) (Thm.prems_of th);
    val allifyied_asm_thms = map (Drule.forall_elim_list cTs o Thm.assume) cterm_asms;
  in (fold (curry op COMP) allifyied_asm_thms th, cterm_asms) end;


(* Given a list of variables that were bound, and a that has been
instantiated with free variable placeholders for the bound vars, it
creates an abstracted version of the theorem, with local bound vars as
lambda-params:

Ts:
("x", ty)

rule::
C :x ==> P :x = Q :x

results in:
("!! x. C x", (%x. p x = %y. p y) [!! x. C x])

note: assumes rule is instantiated
*)
(* Note, we take abstraction in the order of last abstraction first *)
fun mk_abstractedrule ctxt TsFake Ts rule =
  let
    (* now we change the names of temporary free vars that represent
       bound vars with binders outside the redex *)

    val ns =
      IsaND.variant_names ctxt (Thm.full_prop_of rule :: Thm.hyps_of rule) (map fst Ts);

    val (fromnames, tonames, Ts') =
      fold (fn (((faken, _), (n, ty)), n2) => fn (rnf, rnt, Ts'') =>
              (Thm.cterm_of ctxt (Free(faken,ty)) :: rnf,
               Thm.cterm_of ctxt (Free(n2,ty)) :: rnt,
               (n2,ty) :: Ts''))
            (TsFake ~~ Ts ~~ ns) ([], [], []);

    (* rename conflicting free's in the rule to avoid cconflicts
    with introduced vars from bounds outside in redex *)
    val rule' = rule
      |> Drule.forall_intr_list fromnames
      |> Drule.forall_elim_list tonames;

    (* make unconditional rule and prems *)
    val (uncond_rule, cprems) = allify_conditions ctxt (rev Ts') rule';

    (* using these names create lambda-abstracted version of the rule *)
    val abstractions = rev (Ts' ~~ tonames);
    val abstract_rule =
      fold (fn ((n, ty), ct) => Thm.abstract_rule n ct)
        abstractions uncond_rule;
  in (cprems, abstract_rule) end;


(* given names to avoid, and vars that need to be fixed, it gives
unique new names to the vars so that they can be fixed as free
variables *)
(* make fixed unique free variable instantiations for non-ground vars *)
(* Create a table of vars to be renamed after instantiation - ie
      other uninstantiated vars in the hyps of the rule
      ie ?z in C ?z ?x ==> A ?x ?y = B ?x ?y *)
fun mk_renamings ctxt tgt rule_inst =
  let
    val rule_conds = Thm.prems_of rule_inst;
    val (_, cond_vs) =
      fold (fn t => fn (tyvs, vs) =>
        (union (op =) (Misc_Legacy.term_tvars t) tyvs,
         union (op =) (map Term.dest_Var (Misc_Legacy.term_vars t)) vs)) rule_conds ([], []);
    val termvars = map Term.dest_Var (Misc_Legacy.term_vars tgt);
    val vars_to_fix = union (op =) termvars cond_vs;
    val ys = IsaND.variant_names ctxt (tgt :: rule_conds) (map (fst o fst) vars_to_fix);
  in map2 (fn (xi, T) => fn y => ((xi, T), Free (y, T))) vars_to_fix ys end;

(* make a new fresh typefree instantiation for the given tvar *)
fun new_tfree (tv as (ix,sort)) (pairs, used) =
  let val v = singleton (Name.variant_list used) (string_of_indexname ix)
  in ((ix,(sort,TFree(v,sort)))::pairs, v::used) end;


(* make instantiations to fix type variables that are not
   already instantiated (in ignore_ixs) from the list of terms. *)
fun mk_fixtvar_tyinsts ignore_insts ts =
  let
    val ignore_ixs = map fst ignore_insts;
    val (tvars, tfrees) =
      fold_rev (fn t => fn (varixs, tfrees) =>
        (Misc_Legacy.add_term_tvars (t,varixs),
         Misc_Legacy.add_term_tfrees (t,tfrees))) ts ([], []);
    val unfixed_tvars = filter (fn (ix,s) => not (member (op =) ignore_ixs ix)) tvars;
    val (fixtyinsts, _) = fold_rev new_tfree unfixed_tvars ([], map fst tfrees)
  in (fixtyinsts, tfrees) end;


(* cross-instantiate the instantiations - ie for each instantiation
replace all occurrences in other instantiations - no loops are possible
and thus only one-parsing of the instantiations is necessary. *)
fun cross_inst insts =
  let
    fun instL (ix, (ty,t)) = map (fn (ix2,(ty2,t2)) =>
      (ix2, (ty2,Term.subst_vars ([], [(ix, t)]) t2)));

    fun cross_instL ([], l) = rev l
      | cross_instL ((ix, t) :: insts, l) =
          cross_instL (instL (ix, t) insts, (ix, t) :: (instL (ix, t) l));

  in cross_instL (insts, []) end;

(* as above but for types -- I don't know if this is needed, will we ever incur mixed up types? *)
fun cross_inst_typs insts =
  let
    fun instL (ix, (srt,ty)) =
      map (fn (ix2,(srt2,ty2)) => (ix2, (srt2,Term.typ_subst_TVars [(ix, ty)] ty2)));

    fun cross_instL ([], l) = rev l
      | cross_instL ((ix, t) :: insts, l) =
          cross_instL (instL (ix, t) insts, (ix, t) :: (instL (ix, t) l));

  in cross_instL (insts, []) end;


(* assume that rule and target_thm have distinct var names. THINK:
efficient version with tables for vars for: target vars, introduced
vars, and rule vars, for quicker instantiation?  The outerterm defines
which part of the target_thm was modified.  Note: we take Ts in the
upterm order, ie last abstraction first., and with an outeterm where
the abstracted subterm has the arguments in the revered order, ie
first abstraction first.  FakeTs has abstractions using the fake name
- ie the name distinct from all other abstractions. *)

fun rw ctxt ((nonfixed_typinsts, unprepinsts), FakeTs, Ts, outerterm) rule target_thm =
  let
    (* fix all non-instantiated tvars *)
    val (fixtyinsts, othertfrees) = (* FIXME proper context!? *)
      mk_fixtvar_tyinsts nonfixed_typinsts
        [Thm.prop_of rule, Thm.prop_of target_thm];
    val typinsts = cross_inst_typs (nonfixed_typinsts @ fixtyinsts);

    (* certified instantiations for types *)
    val ctyp_insts = TVars.make (map (fn (ix, (s, ty)) => ((ix, s), Thm.ctyp_of ctxt ty)) typinsts);

    (* type instantiated versions *)
    val tgt_th_tyinst = Thm.instantiate (ctyp_insts,Vars.empty) target_thm;
    val rule_tyinst =  Thm.instantiate (ctyp_insts,Vars.empty) rule;

    val term_typ_inst = map (fn (ix,(_,ty)) => (ix,ty)) typinsts;
    (* type instanitated outer term *)
    val outerterm_tyinst = Term.subst_TVars term_typ_inst outerterm;

    val FakeTs_tyinst = map (apsnd (Term.typ_subst_TVars term_typ_inst)) FakeTs;
    val Ts_tyinst = map (apsnd (Term.typ_subst_TVars term_typ_inst)) Ts;

    (* type-instantiate the var instantiations *)
    val insts_tyinst =
      fold_rev (fn (ix, (ty, t)) => fn insts_tyinst =>
        (ix, (Term.typ_subst_TVars term_typ_inst ty, Term.subst_TVars term_typ_inst t))
          :: insts_tyinst) unprepinsts [];

    (* cross-instantiate *)
    val insts_tyinst_inst = cross_inst insts_tyinst;

    (* create certms of instantiations *)
    val cinsts_tyinst =
      Vars.make (map (fn (ix, (ty, t)) => ((ix, ty), Thm.cterm_of ctxt t)) insts_tyinst_inst);

    (* The instantiated rule *)
    val rule_inst = rule_tyinst |> Thm.instantiate (TVars.empty, cinsts_tyinst);

    (* Create a table of vars to be renamed after instantiation - ie
    other uninstantiated vars in the hyps the *instantiated* rule
    ie ?z in C ?z ?x ==> A ?x ?y = B ?x ?y *)
    val renamings = mk_renamings ctxt (Thm.prop_of tgt_th_tyinst) rule_inst;
    val cterm_renamings = map (fn (x, y) => apply2 (Thm.cterm_of ctxt) (Var x, y)) renamings;

    (* Create the specific version of the rule for this target application *)
    val outerterm_inst =
      outerterm_tyinst
      |> Term.subst_Vars (map (fn (ix, (ty, t)) => (ix, t)) insts_tyinst_inst)
      |> Term.subst_Vars (map (fn ((ix, ty), t) => (ix, t)) renamings);
    val couter_inst = Thm.reflexive (Thm.cterm_of ctxt outerterm_inst);
    val (cprems, abstract_rule_inst) =
      rule_inst
      |> Thm.instantiate (TVars.empty, Vars.make (map (apfst (dest_Var o Thm.term_of)) cterm_renamings))
      |> mk_abstractedrule ctxt FakeTs_tyinst Ts_tyinst;
    val specific_tgt_rule =
      Conv.fconv_rule Drule.beta_eta_conversion
        (Thm.combination couter_inst abstract_rule_inst);

    (* create an instantiated version of the target thm *)
    val tgt_th_inst =
      tgt_th_tyinst
      |> Thm.instantiate (TVars.empty, cinsts_tyinst)
      |> Thm.instantiate (TVars.empty, Vars.make (map (apfst (dest_Var o Thm.term_of)) cterm_renamings));

    val (vars,frees_of_fixed_vars) = Library.split_list cterm_renamings;
  in
    Conv.fconv_rule Drule.beta_eta_conversion tgt_th_inst
    |> Thm.equal_elim specific_tgt_rule
    |> Drule.implies_intr_list cprems
    |> Drule.forall_intr_list frees_of_fixed_vars
    |> Drule.forall_elim_list vars
    |> Thm.varifyT_global' (TFrees.make_set othertfrees)
    |-> K Drule.zero_var_indexes
  end;

end;
