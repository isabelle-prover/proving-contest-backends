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
      | CoqExn SP.ExnInfo.{ pp; _ } -> Some (Pp.string_of_ppcmds pp)
    ) ans in
  if List.is_empty error_ans then Ok ()
  else Error (reduce (fun a b -> a ^ "\n" ^ b) error_ans)

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

let pp_command ppf cmd =
  match cmd with
  | Allow_axioms _ -> ()
  | Check (thmname, stmt) ->
    Format.fprintf ppf "@[Check@ %s:@ %s@]%!@." thmname stmt
  | Check_refl stmt ->
    Format.fprintf ppf "@[Check_refl@ %s@]%!@." stmt

type check_result = [`Ok | `OkWithAxioms | `Error]

type command_result =
  | Skip
  | Report_command of {
      name : string;
      result : check_result;
      messages : string list;
    }

let pp_command_result ppf = function
  | Skip -> ()
  | Report_command { name = _; result; messages } ->
    let res_s = function
      | `Ok -> "ok" | `Error -> "error"
      | `OkWithAxioms -> "ok (with axioms)" in
    let pp_msg ppf = Format.fprintf ppf "%s@," in
    Format.fprintf ppf "@[<v>--> %s@,%a@,@]%!"
      (res_s result) (Format.list ~sep:Format.pp_print_cut pp_msg) messages

let check_refl thm =
  add_then_exec ("Goal " ^ thm ^ ". reflexivity. Qed.")
  |> Pair.map2 (function
    | Ok () -> Report_command { name = thm; result = `Ok; messages = [] }
    | Error msg ->
      Report_command { name = thm; result = `Error; messages = [msg] })

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
  if List.is_empty errors then None
  else Some (reduce (fun a b -> a ^ "\n" ^ b) errors)

let check_thm name stmt =
  let lemma_name = "check" in
  let vernac =
    Printf.sprintf "Lemma %s: %s. exact %s. Qed."
      lemma_name stmt name
  in
  add_then_exec vernac
  |> Pair.map2 (function
    | Error msg -> Report_command { name; result = `Error; messages = [msg] }
    | Ok () ->
      match check_assumptions (get_assumptions lemma_name) with
      | None -> Report_command { name; result = `Ok; messages = [] }
      | Some assums ->
        Report_command { name; result = `OkWithAxioms; messages = [assums] })

let run_command (cmd: command) =
  let added_sids, res =
    match cmd with
    | Allow_axioms axs ->
      allowed_axioms := axs @ !allowed_axioms;
      [], Skip
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
  try
    let commands = List.map command_of_sexp input_sexps in
    List.iter (fun s -> add_then_exec s |> ignore) requires;
    List.map (fun command ->
      pp_command Format.std_formatter command;
      let res = run_command command in
      pp_command_result Format.std_formatter res;
      res
    ) commands |> Result.pure
  with Sexplib.Conv.Of_sexp_error (e, sexp) ->
    Format.eprintf "Invalid check file:\n%s\n%a\n"
      (Printexc.to_string e)
      Sexplib.Sexp.pp_hum sexp;
    Error (`Other "Unexpected issue with the checks file. Please report.")

(***************)

let (^/) = Filename.concat
let defs_base = "Defs"
let submission_base = "Submission"
let defs_f = defs_base ^ ".v"
let submission_f = submission_base ^ ".v"
let checks_f = "checks.sexp"
let result_f = "result.json"
let defs dir = dir ^/ defs_f
let submission dir = dir ^/ submission_f
let checks dir = dir ^/ checks_f
let result_file dir = dir ^/ result_f

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
  then Ok ()
  else (
    Printf.eprintf "Incorrect submission directory\n";
    Error (`Other "Unexpected error: incorrect submission directory. Please report.")
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
    spawn_lwt ~workdir ~timeout
      ~timeout_err:(Printf.sprintf "Timeout after %ds: %s" timeout f)
      (Printf.sprintf "coqc -R . %s '%s'" toplevel_namespace f) >>= function
    | Lwt_unix.WEXITED 0 -> Lwt_result.return ()
    | _ -> Lwt_result.fail ("Non-zero exit code when compiling " ^ f)
  in
  Lwt_main.run @@ begin
    compile defs_f >>= fun () ->
    compile submission_f
  end |> function
  | Ok () -> Ok ()
  | Error msg -> Error (`Submission msg)

let check_result_to_yojson = function
  | `Ok -> `String "ok"
  | `OkWithAxioms -> `String "ok_with_axioms"
  | `Error -> `String "error"

type output_check = {
  name : string;
  result : check_result;
} [@@deriving to_yojson]

type output_message = {
  where : string;
  what : string;
} [@@deriving to_yojson]

type output = {
  submission_is_valid : bool;
  checks : output_check list;
  messages : output_message list;
} [@@deriving to_yojson]

let output_of_result
    (res: (command_result list,
           [`Submission of string | `Other of string]) result)
  =
  match res with
  | Error (`Other msg) ->
    { submission_is_valid = false;
      checks = [];
      messages = [{ where = "global"; what = msg }] }
  | Error (`Submission msg) ->
    { submission_is_valid = false;
      checks = [];
      messages = [{ where = submission_f; what = msg }] }
  | Ok checks_res ->
    let checks, messages =
      List.filter_map (function
        | Skip -> None
        | Report_command { name; result; messages } ->
          Some ({ name; result },
                List.map (fun what -> { where = name; what }) messages)
      ) checks_res
      |> List.split
      |> Pair.map2 List.flatten
    in
    { submission_is_valid = true; checks; messages }

let write_result ~file res =
  output_of_result res
  |> output_to_yojson
  |> Yojson.Safe.to_file file

let driver
    timeout debug coq_path ml_path load_path rload_path in_dir
    omit_loc omit_att exn_on_opaque
  =
  let open Result in
  write_result ~file:(result_file in_dir) @@ begin
    (* Build the submission *)
    check_submission_dir in_dir >>= fun () ->
    compile_submission ~timeout in_dir >>= fun () ->
    let in_file = checks in_dir in

    (* Requires for the check file document *)
    let requires = [
      Printf.sprintf "Require Import %s." defs_base;
      Printf.sprintf "Require %s." submission_base;
    ] in

    (* initialization *)
    let options = Serlib.Serlib_init.{ omit_loc; omit_att; exn_on_opaque } in
    Serlib.Serlib_init.init ~options;

    let rload_path =
      (coq_lp_conv ~implicit:true (in_dir, toplevel_namespace)) :: rload_path in
    let iload_path =
      Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path
      @ ml_path @ load_path @ rload_path in
    let _doc, _sid = create_document ~in_file ~iload_path ~debug in

    (* main loop *)
    input_doc ~in_file ~requires
  end

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
    | `Version | `Help | `Ok () -> exit 0
    | `Error _ -> exit 1
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let () = main ()
