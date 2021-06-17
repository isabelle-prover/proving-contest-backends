(* Functions copy-pasted from serapi, which are defined in serapi tools but not
   exposed as library functions *)

(* from sercomp.ml *)
let create_document ~in_file ~stm_flags ~quick ~ml_load_path ~vo_load_path ~debug ~allow_sprop ~indices_matter =

  let open Sertop.Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug
    ; allow_sprop
    ; indices_matter
    } Format.std_formatter;

  (* document initialization *)

  let stm_options = process_stm_flags stm_flags in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = `None
    ; async_proofs_cmd_error_resilience = false
    } in

  let stm_options =
    if quick
    then { stm_options with async_proofs_mode = APonLazy }
    else stm_options
  in

  let injections = [Stm.RequireInjection ("Coq.Init.Prelude", None, Some false)] in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; injections
             ; ml_load_path
             ; vo_load_path
             ; stm_options
             } in

  (* Workaround, see
     https://github.com/ejgallego/coq-serapi/pull/101 *)
  if quick || stm_flags.enable_async <> None
  then Safe_typing.allow_delayed_constants := true;

  Stm.new_doc ndoc

(* From sertop_arg.ml *)
let coq_lp_conv ~implicit (unix_path,lp) = Loadpath.{
    coq_path  = Libnames.dirpath_of_string lp
  ; unix_path
  ; has_ml = true
  ; recursive = true
  ; implicit
  }

(* from sercomp.ml *)
let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let msg = Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1
