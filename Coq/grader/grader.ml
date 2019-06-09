open Containers
open Serapi_utils
module SP = Serapi_protocol
module SA = Serapi_assumptions

let warn ppf =
  Format.eprintf ("Warn: " ^^ ppf)

let reduce f = function
  | [] -> raise (Invalid_argument "reduce")
  | x :: xs -> List.fold_left f x xs

(******)

let default_add_opts =
  SP.{ lim = None; ontop = None; newtip = None; verb = false }

let default_query_opts =
  (* (!) TODO: do the same for default_add_opts? *)
  Sertop_ser.query_opt_of_sexp Sexplib.Sexp.unit

let stateid_max a b =
  if Stateid.compare a b = -1 then b else a

let result_of_ans ans =
  let error_ans =
    List.filter_map (function
      | SP.Ack | Completed -> None
      | ObjList _ -> warn "Unexpected ObjList"; None
      | Canceled _ -> warn "Unexpected Canceled"; None
      | Added _ -> warn "Unexpected Added"; None
      | CoqExn (_,_,_,exn) -> Some exn
    ) ans in
  if List.is_empty error_ans then Ok ()
  else
    Error (
      List.map (fun exn ->
        Sexplib.Sexp.to_string_hum (Sexplib.Conv.sexp_of_exn exn)
      ) error_ans
      |> reduce (fun a b -> a ^ "\n" ^ b)
    )

let add_then_exec stmt =
  let add_ans =
    SP.exec_cmd (SP.Add (
      default_add_opts,
      stmt
    )) in
  let sids = List.filter_map (function
    | SP.Added (sid, _, `NewTip) -> Some sid
    | _ -> None) add_ans in
  let last_tip = List.fold_left stateid_max Stateid.dummy sids in
  let exec_ans = SP.exec_cmd (SP.Exec last_tip) in
  let res = result_of_ans exec_ans in
  sids, res

let get_assumptions name =
  SP.exec_cmd (Query (default_query_opts, Assumptions name))
  |> List.find_map (function
    | SP.ObjList objs ->
      List.find_map (function
        | SP.CoqAssumptions a -> Some a
        | _ -> None) objs
    | _ -> None)
  |> Option.get_exn

include struct
  open Sexplib.Conv

  type command =
    | Allow_axioms of string list
    | Check of string (* theorem name *) *
               string (* expected theorem statement *)
    | Check_refl of string (* theorem statement *)
  [@@deriving sexp]
end

let allowed_axioms : string list ref = ref []

let pp_command pp cmd =
  Sexplib.Sexp.pp_hum pp (sexp_of_command cmd)

let check_refl thm =
  add_then_exec ("Goal " ^ thm ^ ". reflexivity. Qed.")

let check_assumptions (a: SA.t) =
  let explain (ax, _, _) =
    match ax with
    | Printer.Constant c ->
      "Forbidden axiom", Names.Constant.to_string c
    | Printer.Positive mind ->
      "Relies on possibly unsound inductive", Names.MutInd.to_string mind
    | Printer.Guarded c ->
      "Relies on possibly unsound (co)fixpoint", Names.Constant.to_string c
  in
  let errors =
    (if a.SA.type_in_type then ["Relies on type-in-type"] else []) @
    (List.filter_map (fun a ->
       let reason, a_s = explain a in
       if List.mem ~eq:String.equal a_s !allowed_axioms then None
       else Some (Printf.sprintf "%s: %s" reason a_s)
     ) a.SA.axioms)
  in
  if List.is_empty errors then Ok ()
  else Error (
    reduce (fun a b -> a ^ "\n" ^ b) errors
  )

let check_thm name stmt =
  let lemma_name = "check" in
  let vernac =
    Printf.sprintf "Lemma %s: %s. exact %s. Qed."
      lemma_name stmt name
  in
  match add_then_exec vernac with
  | sids, Error e -> sids, Error e
  | sids, Ok () ->
    sids, check_assumptions (get_assumptions lemma_name)

let run_command (cmd: command) =
  let added_sids, res =
    match cmd with
    | Allow_axioms axs ->
      allowed_axioms := axs @ !allowed_axioms;
      [], Ok ()
    | Check_refl thm_statement -> check_refl thm_statement
    | Check (name, stmt) -> check_thm name stmt
  in
  ignore @@ SP.exec_cmd (Cancel added_sids);
  res

let input_doc ~in_file ~requires =
  let input_sexps =
    let cin = open_in in_file in
    let s = Sexplib.Sexp.input_sexps cin in
    close_in cin;
    s
  in
  let commands = List.map command_of_sexp input_sexps in
  List.iter (fun s -> add_then_exec s |> ignore) requires;
  List.iter (fun command ->
    Format.fprintf Format.err_formatter "@[-->@ %a@]@." pp_command command;
    let res = run_command command in
    Format.fprintf Format.err_formatter "@[<--@ %a@]@.@."
      (Result.pp Format.silent) res
  ) commands

(***************)

let (^/) = Filename.concat
let defs_base = "Defs"
let submission_base = "Submission"
let defs_f = defs_base ^ ".v"
let submission_f = submission_base ^ ".v"
let checks_f = "checks.sexp"
let defs dir = dir ^/ defs_f
let submission dir = dir ^/ submission_f
let checks dir = dir ^/ checks_f

let toplevel_namespace = "Top"

let grader_man =
  [
    `S "DESCRIPTION";
    `P "Coq grader.";
    `S "USAGE";
    `P "DIR must contain the following files:"; `Noblank;
    `P "- Defs.v: preliminary definitions as provided by the challenge author;"; `Noblank;
    `P "- Submission.v: the user submission;"; `Noblank;
    `P "- checks.sexp: the check script.";
    `P "The check commands run in an environment corresponding to running \
       $(b,Require Import Defs. Require Submission.). Consequently, names \
       from the submission file have to be qualified in the checks file \
       (e.g. Submission.foo).";
  ]

let grader_doc = "Grader for Coq submissions"

let check_submission_dir dir =
  if Sys.is_directory dir
  && Sys.file_exists (defs dir)
  && Sys.file_exists (submission dir)
  && Sys.file_exists (checks dir)
  then ()
  else (
    Printf.eprintf "Incorrect submission directory\n";
    exit 1
  )

let spawn ~workdir (cmd: string) =
  let pid = Unix.fork () in
  if pid = 0 then (
    Unix.setsid () |> ignore;
    Unix.chdir workdir;
    Unix.execv
      "/bin/sh"
      [| "/bin/sh"; "-c"; cmd |]
  ) else pid

let spawn_lwt ~timeout ~timeout_err ~workdir cmd =
  let open Lwt.Infix in
  let child_pid = spawn ~workdir cmd in
  Lwt.pick [
    (Lwt_unix.sleep (float timeout) >>= fun () ->
     Unix.kill child_pid Sys.sigkill;
     Lwt.return (Error timeout_err));
    (Lwt_unix.waitpid [] child_pid >>= fun (_,status) -> Lwt.return (Ok status));
  ]

let compile_submission ~timeout workdir =
  let open Lwt_result.Infix in
  let compile f =
    spawn_lwt ~workdir ~timeout ~timeout_err:("Timeout: " ^ f)
      (Printf.sprintf "coqc -R . %s '%s'" toplevel_namespace f) >>= function
    | Lwt_unix.WEXITED 0 -> Lwt_result.return ()
    | _ -> Lwt_result.fail ("Non-zero exit code when compiling " ^ f)
  in
  Lwt_main.run @@ begin
    compile defs_f >>= fun () ->
    compile submission_f
  end |> function
  | Ok () -> ()
  | Error msg -> Printf.eprintf "%s\n" msg; exit 1

let driver
    timeout debug coq_path ml_path load_path rload_path in_dir
    omit_loc omit_att exn_on_opaque
  =
  (* Build the submission *)
  check_submission_dir in_dir;
  compile_submission ~timeout in_dir;
  let in_file = checks in_dir in

  (* Requires for the check file document *)
  let requires = [
    Printf.sprintf "Require Import %s." defs_base;
    Printf.sprintf "Require %s." submission_base;
  ] in

  (* initialization *)
  let options = Serlib_init.{ omit_loc; omit_att; exn_on_opaque } in
  Serlib_init.init ~options;

  let rload_path =
    (coq_lp_conv ~implicit:true (in_dir, toplevel_namespace)) :: rload_path in
  let iload_path =
    Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path
    @ ml_path @ load_path @ rload_path in
  let doc, _sid = create_document ~in_file ~iload_path ~debug in

  (* main loop *)
  let () = input_doc ~in_file ~requires in
  close_document ~doc ()

let main () =
  let open Cmdliner in

  let input_dir =
    let doc = "Input directory containing the submission." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"DIR" ~doc)
  in
  let timeout =
    let doc = "Time limit when compiling the submission" in
    Arg.(value & opt int 60 & info ["timeout"] ~docv:"SECONDS" ~doc)
  in

  let main_cmd =
    let open Sertop_arg in
    Term.(const driver
          $ timeout $ debug $ prelude
          $ ml_include_path $ load_path $ rload_path $ input_dir $ omit_loc
          $ omit_att $ exn_on_opaque
         ),
    Term.info "grader" ~doc:grader_doc ~man:grader_man
  in

  try match Term.eval ~catch:false main_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let () = main ()
