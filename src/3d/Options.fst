module Options
open HashingOptions
open FStar.All
open FStar.ST
module U8 = FStar.UInt8
module OS = OS

#push-options "--warn_error -272" //top-level effects are okay

inline_for_extraction
let valid_string
  (valid: (string -> Tot bool))
: Tot Type0
= (s: string { valid s == true })

let always_valid (_: string) : Tot bool = true

inline_for_extraction
let vstring = valid_string always_valid

(* NOTE: default arguments here MUST be set to false, [] or None *)

let arg0 : ref (option vstring) = alloc None
let batch : ref bool = alloc false
let clang_format : ref bool = alloc false
let clang_format_executable : ref (option vstring) = alloc None
let cleanup : ref bool = alloc false
let debug : ref bool = alloc false
let inplace_hashes : ref (list vstring) = alloc []
let input_file : ref (list string) = alloc []
let json : ref bool = alloc false
let no_copy_everparse_h : ref bool = alloc false
let output_dir : ref (option vstring) = alloc None
let save_hashes : ref bool = alloc false
let skip_c_makefiles : ref bool = alloc false
let skip_deps: ref bool = alloc false
let skip_o_rules: ref bool = alloc false

let valid_micro_step (str: string) : Tot bool = match str with
  | "verify"
  | "extract"
  | "copy_clang_format"
    -> true
  | _ -> false

let micro_step : ref (option (valid_string valid_micro_step)) = alloc None

let produce_c_from_existing_krml : ref bool = alloc false

let valid_makefile (str: string) : Tot bool = match str with
  | "gmake"
  | "nmake"
  -> true
  | _ -> false

let makefile : ref (option (valid_string valid_makefile)) = alloc None
let makefile_name : ref (option vstring) = alloc None

let valid_equate_types (str: string) : Tot bool =
     let l = String.split [','] str in
     match l with
     | [m1;m2] -> true
     | _ -> false

let equate_types_list : ref (list (valid_string valid_equate_types)) = alloc []

let valid_check_hashes : string -> Tot bool = function
| "weak"
| "strong"
| "inplace"
  -> true
| _ -> false

let check_hashes : ref (option (valid_string valid_check_hashes)) = alloc None

noeq
type cmd_option_kind =
  | OptBool:
      (v: ref bool) ->
      cmd_option_kind
  | OptStringOption:
      (arg_desc: string) ->
      (valid: (string -> Tot bool)) ->
      (v: ref (option (valid_string valid))) ->
      cmd_option_kind
  | OptList:
      (arg_desc: string) ->
      (valid: (string -> Tot bool)) ->
      (v: ref (list (valid_string valid))) ->
      cmd_option_kind

noeq
type cmd_option
= | CmdOption:
    (name: string) ->
    (kind: cmd_option_kind) ->
    (desc: string) ->
    (implies: list string) (* name of OptBool to set to true *) ->
    cmd_option
  | CmdFStarOption of FStar.Getopt.opt

let cmd_option_name (a: cmd_option) : Tot string =
  match a with
  | CmdFStarOption (_, name', _, _)
  | CmdOption name' _ _ _
    -> name'

let rec find_cmd_option (name: string) (l: list cmd_option): Tot (option cmd_option) = match l with
  | [] -> None
  | a :: q ->
    if name = cmd_option_name a then Some a else find_cmd_option name q

let cmd_option_description (a: cmd_option) : Tot string =
  match a with
  | CmdOption _ _ desc _
  | CmdFStarOption (_, _, _, desc) ->
    desc

let cmd_option_arg_desc (a: cmd_option) : Tot string =
  match a with
  | CmdFStarOption (_, _, arg, _) ->
    begin match arg with
    | FStar.Getopt.OneArg (_, argdesc) -> argdesc
    | _ -> ""
    end
  | CmdOption _ kind _ _ ->
    begin match kind with
    | OptStringOption argdesc _ _
    | OptList argdesc _ _
      -> argdesc
    | _ -> ""
    end

let set_implies (options: ref (list cmd_option)) (implies: list string) : ML unit =
  List.iter
    (fun name ->
      match find_cmd_option name !options with
      | Some (CmdOption _ (OptBool x) _ _) -> x := true
      | _ -> ()
    )
    implies

let string_starts_with (big small: string) : Tot bool =
  let small_len = String.length small in
  if String.length big < small_len
  then false
  else String.sub big 0 small_len = small

let negate_string_gen (s: string) (negation: string) =
  if s `string_starts_with` negation
  then String.sub s (String.length negation) (String.length s - String.length negation)
  else negation ^ s

let name_is_negated (s: string) : Tot bool = s `string_starts_with` "no_"
let negate_name (s: string) : Tot string = negate_string_gen s "no_"
let negate_description (s: string) : Tot string = negate_string_gen s "Do not"

let fstar_options_of_cmd_option
  (options: ref (list cmd_option))
  (o: cmd_option)
: Tot (list FStar.Getopt.opt)
= match o with
  | CmdFStarOption f -> [f]
  | CmdOption name kind desc implies ->
    begin match kind with
    | OptBool v ->
      [
        (FStar.Getopt.noshort, name, FStar.Getopt.ZeroArgs (fun _ -> set_implies options implies; v := true), desc);
        (FStar.Getopt.noshort, negate_name name, FStar.Getopt.ZeroArgs (fun _ -> v := false), negate_description desc);
      ]
    | OptStringOption arg_desc valid v ->
      [
        (
          FStar.Getopt.noshort, name,
          FStar.Getopt.OneArg (
            (fun (x: string) ->
              if valid x
              then begin
                set_implies options implies;
                v := Some x
              end else
                failwith (Printf.sprintf "Bad argument to %s: got %s, expected %s" name x arg_desc)
            ),
            arg_desc
          ),
          desc
        );
        (FStar.Getopt.noshort, negate_name name, FStar.Getopt.ZeroArgs (fun _ -> v := None), negate_description desc)
      ]
    | OptList arg_desc valid v ->
      [
        (
          FStar.Getopt.noshort, name,
          FStar.Getopt.OneArg (
            (fun (x: string) ->
              if valid x
              then begin
                set_implies options implies;
                v := x :: !v
              end else
                failwith (Printf.sprintf "Bad argument to %s: got %s, expected %s" name x arg_desc)
            ),
            arg_desc
          ),
          desc
        );
        (
          FStar.Getopt.noshort, negate_name name,
          FStar.Getopt.ZeroArgs (fun _ -> v := []),
          desc
        );
      ]
    end

let compute_current_options (options: ref (list cmd_option)) (ignore: list string) : ML string =
  (* we would like to output a normalized sequence of options so that its semantics does not depend on whether any other options are prepended (i.e. whether 3d is run from 3d or from everparse.cmd or from everparse.sh *)
  (* first print the values of current options except untoggled boolean options *)
  let print (msg: string) (opt: cmd_option) : ML string =
    if List.Tot.mem (cmd_option_name opt) ignore
    then msg
    else
    match opt with
    | CmdOption name kind desc implies ->
      begin match kind with
      | OptBool v ->
        if !v
        then Printf.sprintf "%s --%s" msg name
        else msg
      | OptStringOption _ _ v ->
        begin match !v with
        | None -> Printf.sprintf "%s --%s" msg (negate_name name)
        | Some v -> Printf.sprintf "%s --%s %s" msg name v
        end
      | OptList _ _ v ->
        let v = !v in
        let msg = Printf.sprintf "%s --%s" msg (negate_name name) in
        let app (msg: string) (s: string) = Printf.sprintf "%s --%s %s" msg name s in
        List.Tot.fold_left app msg (List.Tot.rev v) (* list was accumulated as a fifo *)
      end
    | _ -> msg
  in
  let msg = List.fold_left print "" !options in
  (* then print the untoggled boolean options *)
  let print_untoggle (msg: string) (opt: cmd_option) : ML string =
    match opt with
    | CmdOption name (OptBool v) _ _ ->
      if (if not (List.Tot.mem name ignore) then not !v else false)
      then Printf.sprintf "%s --%s" msg (negate_name name)
      else msg
    | _ -> msg
  in
  List.fold_left print_untoggle msg !options

let get_arg0 () : ML string =
  match !arg0 with
  | None -> "3d"
  | Some v -> v

let display_usage_1 (options: ref (list cmd_option)) : ML unit =
  FStar.IO.print_string "EverParse/3d: verified data validation with dependent data descriptions\n";
  FStar.IO.print_string "\n";
  FStar.IO.print_string (Printf.sprintf "Usage: %s [options] path_to_input_file1.3d path_to_input_file2.3d ... \n" (get_arg0 ()));
  FStar.IO.print_string "\n";
  FStar.IO.print_string "Options:\n";
  List.iter
    (fun x ->
      let m = cmd_option_name x in
      let desc = cmd_option_description x in
      let argdesc = cmd_option_arg_desc x in
      let argdesc = if argdesc = "" then "" else Printf.sprintf "<%s>" argdesc in
      let negate = if CmdOption? x then Printf.sprintf " (opposite is --%s)" (negate_name m) else "" in
      let visible = not (m `string_starts_with` "__") in
      if visible then FStar.IO.print_string (Printf.sprintf "--%s%s%s\n\t%s\n" m argdesc negate desc)
    )
    !options
    ;
  FStar.IO.print_string (Printf.sprintf "\nCurrent options are:%s\n" (compute_current_options options []))

let (display_usage_2, compute_options_2, fstar_options) =
  let options : ref (list cmd_option) = alloc [] in
  let display_usage () = display_usage_1 options in
  let compute_options = compute_current_options options in
  options := [
    CmdOption "batch" (OptBool batch) "Verify the generated F* code and extract C code" [];
    CmdOption "check_hashes" (OptStringOption "weak|strong|inplace" valid_check_hashes check_hashes) "Check hashes" ["batch"];
    CmdOption "check_inplace_hash" (OptList "file.3d=file.h" always_valid inplace_hashes) "Check hashes stored in one .h/.c file" [];
    CmdOption "clang_format" (OptBool clang_format) "Call clang-format on extracted .c/.h files (--batch only)" ["batch"];
    CmdOption "clang_format_executable" (OptStringOption "clang-format full path" always_valid clang_format_executable) "Set the path to clang-format if not reachable through PATH" ["batch"; "clang_format"];
    CmdOption "cleanup" (OptBool cleanup) "Remove *.fst*, *.krml and kremlin-args.rsp (--batch only)" [];
    CmdOption "no_copy_everparse_h" (OptBool no_copy_everparse_h) "Do not Copy EverParse.h (--batch only)" [];
    CmdOption "debug" (OptBool debug) "Emit a lot of debugging output" [];
    CmdFStarOption ('h', "help", FStar.Getopt.ZeroArgs (fun _ -> display_usage (); exit 0), "Show this help message");
    CmdOption "json" (OptBool json) "Dump the AST in JSON format" [];
    CmdOption "makefile" (OptStringOption "gmake|nmake" valid_makefile makefile) "Do not produce anything, other than a Makefile to produce everything" [];
    CmdOption "makefile_name" (OptStringOption "some file name" always_valid makefile_name) "Name of the Makefile to produce (with --makefile, default <output directory>/EverParse.Makefile" [];
    CmdOption "odir" (OptStringOption "output directory" always_valid output_dir) "output directory (default '.'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory" [];
    CmdOption "save_hashes" (OptBool save_hashes) "Save hashes" [];
    CmdOption "skip_c_makefiles" (OptBool skip_c_makefiles) "Do not Generate Makefile.basic, Makefile.include" [];
    CmdOption "skip_o_rules" (OptBool skip_o_rules) "With --makefile, do not generate rules for .o files" [];
    CmdFStarOption (let open FStar.Getopt in noshort, "version", ZeroArgs (fun _ -> FStar.IO.print_string (Printf.sprintf "EverParse/3d %s\nCopyright 2018, 2019, 2020 Microsoft Corporation\n" Version.everparse_version); exit 0), "Show this version of EverParse");
    CmdOption "equate_types" (OptList "an argument of the form A,B, to generate asserts of the form (A.t == B.t)" valid_equate_types equate_types_list) "Takes an argument of the form A,B and then for each entrypoint definition in B, it generates an assert (A.t == B.t) in the B.Types file, useful when refactoring specs, you can provide multiple equate_types on the command line" [];
    CmdOption "__arg0" (OptStringOption "executable name" always_valid arg0) "executable name to use for the help message" [];
    CmdOption "__micro_step" (OptStringOption "verify|extract" valid_micro_step micro_step) "micro step" [];
    CmdOption "__produce_c_from_existing_krml" (OptBool produce_c_from_existing_krml) "produce C from .krml files" [];
    CmdOption "__skip_deps" (OptBool skip_deps) "skip dependency analysis, assume all dependencies are specified on the command line" [];
  ];
  let fstar_options =
    List.Tot.concatMap (fstar_options_of_cmd_option options) !options
  in
  (display_usage, compute_options, fstar_options)

let display_usage = display_usage_2

let compute_options = compute_options_2

let parse_cmd_line () : ML (list string) =
  let open FStar.Getopt in
  let res = FStar.Getopt.parse_cmdline fstar_options (fun file -> input_file := file :: !input_file) in
  match res with
  | Success -> !input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let split_3d_file_name fn =
  let fn = OS.basename fn in
  if OS.extension fn = ".3d"
  then Some (OS.remove_extension fn)
  else None

let get_file_name mname = mname ^ ".3d"

let get_module_name (file: string) =
    match split_3d_file_name file with
    | Some nm -> nm
    | None -> "DEFAULT"

let get_output_dir () =
  match !output_dir with
  | None -> "."
  | Some s -> s

let debug_print_string (s:string): ML unit =
  if !debug
  then FStar.IO.print_string s
  else ()

let get_batch () =
  !batch

let get_clang_format () =
  !clang_format

let get_clang_format_executable () =
  match !clang_format_executable with
  | None -> ""
  | Some s -> s

let get_cleanup () =
  !cleanup

let get_skip_c_makefiles () =
  !skip_c_makefiles

let get_no_everparse_h () =
  !no_copy_everparse_h

let get_check_hashes () =
  if !batch then match !check_hashes with
  | None -> None
  | Some "weak" -> Some WeakHashes
  | Some "strong" -> Some StrongHashes
  | Some "inplace" -> Some InplaceHashes
  else None

let get_save_hashes () =
  !save_hashes

let get_check_inplace_hashes () =
  List.rev !inplace_hashes

let get_equate_types_list () =
  List.map
    (fun (x: valid_string valid_equate_types) ->
      let [a; b] = String.split [','] x in (a, b)
    )
    !equate_types_list

let get_micro_step _ =
  match !micro_step with
  | None -> None
  | Some "verify" -> Some MicroStepVerify
  | Some "extract" -> Some MicroStepExtract
  | Some "copy_clang_format" -> Some MicroStepCopyClangFormat

let get_produce_c_from_existing_krml _ =
  !produce_c_from_existing_krml

let get_skip_deps _ =
  !skip_deps

let get_makefile _ =
  match !makefile with
  | None -> None
  | Some "gmake" -> Some MakefileGMake
  | Some "nmake" -> Some MakefileNMake

let get_makefile_name _ =
  match !makefile_name with
  | None -> OS.concat (get_output_dir ()) "EverParse.Makefile"
  | Some mf -> mf

let get_skip_o_rules _ =
  !skip_o_rules

let get_json () =
  !json
