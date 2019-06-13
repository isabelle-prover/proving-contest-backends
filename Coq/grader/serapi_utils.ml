(* Functions copy-pasted from serapi *)

let create_document ~in_file ~iload_path ~debug =
  let open Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug
    };

  (* document initialization *)

  let stm_options = process_stm_flags
      { enable_async  = None
      ; deep_edits    = false
      ; async_workers = 1
      } in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = `None
    ; async_proofs_cmd_error_resilience = false
    } in

  let require_libs = ["Coq.Init.Prelude", None, Some false] in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; require_libs
             ; iload_path
             ; stm_options
             } in

  Stm.new_doc ndoc

(* From sertop_arg.ml *)
let coq_lp_conv ~implicit (unix_path,lp) = Mltop.{
    path_spec = VoPath {
        coq_path  = Libnames.dirpath_of_string lp;
        unix_path;
        has_ml    = AddRecML;
        implicit;
      };
    recursive = true;
  }

let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let msg = Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1
