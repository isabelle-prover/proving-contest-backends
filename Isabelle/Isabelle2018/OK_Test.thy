theory OK_Test
imports Main
keywords
  "save_test_theory" :: thy_decl and
  "safe_definition" :: thy_decl and
  "test" :: thy_goal and
  "good_sorry" :: "qed" % "proof"
begin

section \<open>Handling of sorry\<close>

ML \<open>
fun local_skip_proof int state =
  Proof.local_terminal_proof ((Method.sorry_text int, Position.no_range), NONE) state before
  (K ()) (Proof.context_of state);

fun global_skip_proof int state =
  Proof.global_terminal_proof ((Method.sorry_text int, Position.no_range), NONE) state before
  (K ()) (Proof.context_of state);

val local_skip_proof = Toplevel.proof' local_skip_proof;
val global_skip_proof = Toplevel.end_proof global_skip_proof;
val skip_proof = local_skip_proof o global_skip_proof;

val _ =
  Outer_Syntax.command @{command_keyword good_sorry} "skip proof (quick-and-dirty mode only!)"
    (Scan.succeed skip_proof);
\<close>

ML \<open>
val get_oracles = Proofterm.all_oracles_of o Proofterm.strip_thm o Thm.proof_body_of

val contains_sorry = exists (fn (a, _) => a = "Pure.skip_proof") o get_oracles

fun report_sorry ctxt =
  if Context_Position.is_visible ctxt then
    Output.report [Markup.markup (Markup.bad ()) "Proof arises from sorry oracle!"]
  else ();

fun check_sorry ctxt thm =
    if contains_sorry thm then report_sorry ctxt else ()

fun score namedthms =
    let
      val scores = map (contains_sorry o snd) namedthms
      val names = map fst namedthms
      val sn = ListPair.zip (scores,names)
      fun spit [] = ""
        | spit ((s,n)::sns) = let
            val str = n ^ ":" ^ (if s then "failed" else "passed")
          in
            "\n" ^ str ^ spit sns
        end 
    in
       writeln ("grading:" ^ spit sn)
    end


\<close>

(*
(* Usage: *)
lemma one_add_1_eq_3:
  "1 + 1 = 3"
  good_sorry

ML \<open>check_sorry @{context} @{thm HOL.refl}\<close>
ML \<open>check_sorry @{context} @{thm one_add_1_eq_3}\<close>
*)

section \<open>Check theorems in saved context\<close>

ML\<open>

datatype thy = THY of theory option;

fun thy_merge _ (THY NONE, THY NONE) = THY NONE
  | thy_merge _ (THY (SOME t), THY NONE) = THY (SOME t)
  | thy_merge _ (THY NONE, THY (SOME t)) = THY (SOME t)
  | thy_merge e (THY (SOME x), THY (SOME y)) = if Context.eq_thy (x, y) then THY (SOME x) else e ();

structure Data = Generic_Data
(
  type T = thy
  val empty = THY NONE
  val extend = I
  val merge = thy_merge (fn _ => error "merge error")
);

fun mk_thy thy = THY (SOME thy);

fun thy_of_thy (THY g) = g

fun get_thy_generic context = Data.get context |> thy_of_thy;

fun get_thy ctxt = get_thy_generic (Context.Proof ctxt)

fun update_theory thy ctxt =
  Data.map (fn thy' => thy_merge (fn _ => error "theory already saved") (mk_thy thy, thy')) ctxt;

fun save_test_theory lthy = Local_Theory.declaration {syntax = false, pervasive = true}
  (fn _ => update_theory (Proof_Context.theory_of lthy)) lthy


fun test raw_t lthy =
  let
    val thy = if is_some (get_thy lthy) then the (get_thy lthy) else error "the theory was not saved"
    val t = Syntax.read_term (Proof_Context.init_global thy) raw_t
    val T = fastype_of t
    val goal = if T = propT then t else
      (if T = HOLogic.boolT then HOLogic.mk_Trueprop t else error "wrong type")
  in
    Proof.theorem NONE (K I) [[(goal, [])]] lthy
  end;

val _ =
  Outer_Syntax.local_theory @{command_keyword save_test_theory}
    "save test theory"
      (Scan.succeed save_test_theory);


val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword test}
    "test"
    (Parse.term >> test);
\<close>

(* Put in Defs.thy *)
(* save_test_theory *)

(*
definition False where [simp]:  "False = True"

lemma False
  by auto

(* Put in Check.thy *)
test "False"
  by auto
*)

section \<open>Safe Definition\<close>

ML\<open>
fun safe_definition raw_var ((a, raw_atts), raw_spec) lthy =
let
  val thy = if is_some (get_thy lthy) then the (get_thy lthy) else error "the theory was not saved"
  val var = Proof_Context.read_var raw_var (Proof_Context.init_global thy) |> fst
  val rhs = Syntax.read_term lthy raw_spec
  val T = fastype_of rhs
  val atts = map (Attrib.check_src lthy) raw_atts
  val lhs = Free (Binding.name_of (#1 var), T)
  val spec = Logic.mk_equals (lhs, rhs)
  val name = Thm.def_binding_optional (#1 var) a;
in
  Specification.definition (SOME var) [] [] ((name, atts), spec) lthy |> snd
end;

val constdecl =
  Parse.binding --
    (@{keyword "is"} >> K (NONE, NoSyn) ||
      Parse.$$$ "::" |-- Parse.!!! ((Parse.typ >> SOME) -- Parse.opt_mixfix' --| @{keyword "is"}) ||
      Scan.ahead (Parse.$$$ "(") |-- Parse.!!! (Parse.mixfix' --| @{keyword "is"} >> pair NONE))
  >> Scan.triple2;

val _ =
  Outer_Syntax.local_theory @{command_keyword safe_definition} "safe constant definition"
    (constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.term)
      >> (fn (decl, spec) =>
        safe_definition decl spec));
\<close>

(*
safe_definition bla :: bool is xxx[simp]: False
print_theorems
*)

end
