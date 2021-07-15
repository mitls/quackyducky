module Main
open FStar.IO
open FStar.All
open Ast
open ParserDriver
module T = Target
open FStar.ST
#push-options "--z3rlimit_factor 2"

let open_write_file (s:string) : ML FStar.IO.fd_write =
  FStar.IO.print_string (FStar.Printf.sprintf "Writing file %s\n" s);
  FStar.IO.open_write_file s

let parse_prog (fn:string) : ML prog =
  let decls, type_refinement_opt = ParserDriver.parse fn in
  if decls
     |> List.tryFind is_entrypoint_or_export
     |> Some?
  then decls, type_refinement_opt
  else raise (Error (Printf.sprintf "File %s does not have an entry point or an exported definition, exiting\n" fn))

noeq
type env = {
  binding_env : Binding.global_env;
  typesizes_env : TypeSizes.size_env;
  translate_env : Translate.translate_env
}

let initial_env () : ML env = {
  binding_env = Binding.initial_global_env ();
  typesizes_env = TypeSizes.initial_senv ();
  translate_env = Translate.initial_translate_env ();
}

let translate_module (en:env) (mname:string) (fn:string)
  : ML (list Ast.decl &
        list Target.decl &
        StaticAssertions.static_asserts &
        env) =

  Options.debug_print_string (FStar.Printf.sprintf "Processing file: %s\nModule name: %s\n" fn mname);
  let decls, refinement = parse_prog fn in


  Options.debug_print_string "=============After parsing=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, refinement = Desugar.desugar mname (decls, refinement) in

  Options.debug_print_string "=============After desugaring=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, benv = Binding.bind_decls en.binding_env decls in

  Options.debug_print_string "=============After binding=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  if Options.get_json()
  then (
    IO.print_string (JSON.prog_to_json (decls, refinement));
    IO.print_string "\n"
  );
  
  let decls = BitFields.eliminate benv decls in
  
  Options.debug_print_string "=============After bitflds=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";
  
  let decls, senv = TypeSizes.size_of_decls benv en.typesizes_env decls in

  let static_asserts = StaticAssertions.compute_static_asserts benv senv refinement in
  
  let decls = Simplify.simplify_prog benv senv decls in
  
  Options.debug_print_string "=============After simplify============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls = InlineSingletonRecords.simplify_prog decls in
  
  Options.debug_print_string "=============After inline singletons============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";
  
  let t_decls, tenv = Translate.translate_decls benv senv en.translate_env decls in

   decls,
   t_decls,
   static_asserts,
   { binding_env = benv;
     typesizes_env = senv;
     translate_env = tenv }

let emit_fstar_code (en:env) (modul:string) (t_decls:list Target.decl)
  (static_asserts:StaticAssertions.static_asserts)
  : ML unit =

  let types_fst_file =
    open_write_file
      (Printf.sprintf "%s/%s.Types.fst"
        (Options.get_output_dir ())
        modul) in
  FStar.IO.write_string types_fst_file (Target.print_types_decls modul t_decls);
  FStar.IO.close_write_file types_fst_file;

  let fst_file =
    open_write_file
      (Printf.sprintf "%s/%s.fst"
        (Options.get_output_dir())
        modul) in
  FStar.IO.write_string fst_file (Target.print_decls modul t_decls);
  FStar.IO.close_write_file fst_file;

  let fsti_file =
    open_write_file
      (Printf.sprintf "%s/%s.fsti"
        (Options.get_output_dir())
        modul) in
  FStar.IO.write_string fsti_file (Target.print_decls_signature modul t_decls);
  FStar.IO.close_write_file fsti_file;

  //print wrapper only if there is an entrypoint
  if List.tryFind (fun (d, _) ->
    let open Target in
    match d with
    | Type_decl td -> td.decl_name.td_entrypoint
    | _ -> false) t_decls |> Some?
  then begin
    let wrapper_header, wrapper_impl = Target.print_c_entry modul en.binding_env t_decls in

    let c_file =
      open_write_file
        (Printf.sprintf "%s/%sWrapper.c"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string c_file wrapper_impl;
    FStar.IO.close_write_file c_file;

    let h_file =
      open_write_file
        (Printf.sprintf "%s/%sWrapper.h"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string h_file wrapper_header;
    FStar.IO.close_write_file h_file
  end;

  if StaticAssertions.has_static_asserts static_asserts then begin
    let c_static_asserts_file =
      open_write_file
        (Printf.sprintf "%s/%sStaticAssertions.c"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string c_static_asserts_file (StaticAssertions.print_static_asserts static_asserts);
    FStar.IO.close_write_file c_static_asserts_file
  end

let process_file (en:env) (fn:string) (modul:string) (emit_fstar:bool) : ML env =
  let _decls, t_decls, static_asserts, en =
    translate_module en modul fn in
  if emit_fstar then emit_fstar_code en modul t_decls static_asserts
  else IO.print_string (Printf.sprintf "Not emitting F* code for %s\n" fn);

  let ds = Binding.get_exported_decls en.binding_env modul in
  
  { binding_env = Binding.finish_module en.binding_env modul ds;
    typesizes_env = TypeSizes.finish_module en.typesizes_env modul ds;
    translate_env = Translate.finish_module en.translate_env modul ds }

let process_files (files_and_modules:list (string & string)) (emit_fstar:string -> ML bool) : ML unit =
  IO.print_string (Printf.sprintf "Processing files: %s\n"
    (List.fold_left (fun acc fn ->
      Printf.sprintf "%s %s" acc fn) "" (List.map fst files_and_modules)));
  let env = initial_env () in
  files_and_modules
  |> List.fold_left (fun env (fn, modul) ->
                    process_file env fn modul (emit_fstar modul)) env
  |> ignore

let produce_and_postprocess_c
  (out_dir: string)
  (file: string)
: ML unit
=
  let modul = Options.get_module_name file in
  let deps = Deps.collect_and_sort_dependencies [file] in
  let dep_files_and_modules = List.map (fun f -> (f, Options.get_module_name f)) deps in
  (* remove the current module from the deps *)
  let dep_files_and_modules = List.filter (fun (_, m) -> m <> modul) dep_files_and_modules in
  Batch.produce_and_postprocess_one_c
    (Options.get_clang_format ())
    (Options.get_clang_format_executable ())
    out_dir
    file
    modul
    dep_files_and_modules

let go () : ML unit =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let cmd_line_files = Options.parse_cmd_line() in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options.get_check_inplace_hashes () in
  if Cons? inplace_hashes
  then Batch.check_inplace_hashes inplace_hashes
  else
  let micro_step = Options.get_micro_step () in
  if micro_step = Some HashingOptions.MicroStepCopyClangFormat
  then
  (* Special mode: --__micro_step copy_clang_format *)
    let _ = Batch.copy_clang_format (Options.get_output_dir ()) in
    exit 0
  else
  (* for other modes, a nonempty list of files is needed on the command line, so if none are there, then we shall print the help message *)
  if Nil? cmd_line_files
  then let _ = Options.display_usage () in exit 1
  else
  let out_dir = Options.get_output_dir () in
  (* Special mode: --__micro_step *)
  match micro_step with
  | Some step ->
    let f = match step with
    | HashingOptions.MicroStepExtract -> Batch.extract_fst_file
    | HashingOptions.MicroStepVerify -> Batch.verify_fst_file
    in
    List.iter (f out_dir) cmd_line_files
  | None ->
  (* Special mode: --makefile" *)
  match Options.get_makefile () with
  | Some t ->
    GenMakefile.write_makefile
      t
      (Options.get_skip_o_rules ())
      (Options.get_clang_format ())
      cmd_line_files
  | None ->
  (* Special mode: --__produce_c_from_existing_krml *)
  if Options.get_produce_c_from_existing_krml ()
  then
    let _ = List.iter
      (produce_and_postprocess_c out_dir)
      cmd_line_files
    in
    FStar.IO.print_string "EverParse succeeded!\n"
  else
  (* for other modes, the list of files provided on the command line is assumed to be a list of .3d files, and the list of all .3d files in dependency order has to be inferred from the list of .3d input files provided by the user, unless --__skip_deps is provided *)
  let all_files =
    if Options.get_skip_deps ()
    then List.Tot.rev cmd_line_files (* files are accumulated in reverse on the command line *)
    else Deps.collect_and_sort_dependencies cmd_line_files
  in
  let all_files_and_modules = List.map (fun file -> (file, Options.get_module_name file)) all_files in
  (* Special mode: --check_hashes *)
  let check_hashes = Options.get_check_hashes () in
  if Some? check_hashes
  then Batch.check_all_hashes (Some?.v check_hashes) out_dir all_files_and_modules
  else
  (* Default mode: process .3d files *)
  let should_emit_fstar_code : string -> ML bool =
    let cmd_line_modules = List.map Options.get_module_name cmd_line_files in
    fun modul ->
      let b = Options.get_batch () in
      b || List.Tot.mem modul cmd_line_modules in
  process_files all_files_and_modules should_emit_fstar_code;
  (* we need to pretty-print source modules in all cases, regardless of --batch,
     because of the Makefile scenario
   *)
   (*
    * pretty print only the modules we emitted code for
    *)
  Batch.pretty_print_source_modules out_dir
    (List.filter (fun (_, m) -> should_emit_fstar_code m) all_files_and_modules);
  (* Sub-mode of the default mode: --batch *)
  if Options.get_batch ()
  then
  let _ = Batch.postprocess_fst
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_c_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir all_files_and_modules
  in
  FStar.IO.print_string "EverParse succeeded!\n"
  else
    (* If --batch is not set, then we also need to postprocess the wrappers and assertions
       (copyright header and clang-format) *)
    Batch.postprocess_wrappers
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        out_dir all_files_and_modules

#push-options "--warn_error -272" //top-level effects are okay
#push-options "--admit_smt_queries true" //explicitly not handling all exceptions, so that we can meaningful backtraces
let _ =
  try go()
  with
    | Error msg ->
      FStar.IO.print_string msg;
      exit 1
#pop-options
