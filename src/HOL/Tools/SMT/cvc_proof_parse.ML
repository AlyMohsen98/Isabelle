(*  Title:      HOL/Tools/SMT/cvc_proof_parse.ML
    Author:     Jasmin Blanchette, TU Muenchen

CVC4 and cvc5 proof (actually, unsat core) parsing.
*)

signature CVC_PROOF_PARSE =
sig
  val parse_proof: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
end;

structure CVC_Proof_Parse: CVC_PROOF_PARSE =
struct

fun parse_proof ({ll_defs, assms, ...} : SMT_Translate.replay_data) xfacts prems _ output =
  if exists (String.isPrefix "(error \"This build of CVC4 doesn't have proof support") output then
    {outcome = NONE, fact_ids = NONE, atp_proof = K []}
  else
    let
      val num_ll_defs = length ll_defs

      val id_of_index = Integer.add num_ll_defs
      val index_of_id = Integer.add (~ num_ll_defs)

      val used_assert_ids =
        map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) output
      val used_assm_js =
        map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
          used_assert_ids

      val conjecture_i = 0
      val prems_i = conjecture_i + 1
      val num_prems = length prems
      val facts_i = prems_i + num_prems

      val fact_ids' =
        map_filter (fn j =>
          let val ((i, _), _) = nth assms j in
            try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
          end) used_assm_js
    in
      {outcome = NONE, fact_ids = SOME fact_ids', atp_proof = K []}
    end

end;
