module Options
open HashingOptions
open FStar.All

val display_usage : unit -> ML unit

val compute_options (ignore: list string) : ML string

val parse_cmd_line : unit -> ML (list string)

val get_file_name (mname:string) : ML string

val get_module_name (file: string) : ML string

val get_output_dir : unit -> ML string

val debug_print_string (s:string) : ML unit

val get_batch : unit -> ML bool

val get_clang_format : unit -> ML bool

val get_clang_format_executable : unit -> ML string

val get_cleanup : unit -> ML bool

val get_skip_c_makefiles : unit -> ML bool

val get_no_everparse_h : unit -> ML bool

val get_check_hashes : unit -> ML (option check_hashes_t)

val get_save_hashes : unit -> ML bool

val get_check_inplace_hashes : unit -> ML (list string)

val get_equate_types_list : unit -> ML (list (string & string))

val get_micro_step : unit -> ML (option micro_step_t)

val get_produce_c_from_existing_krml : unit -> ML bool

val get_skip_deps : unit -> ML bool

val get_makefile : unit -> ML (option makefile_type)

val get_makefile_name : unit -> ML string

val get_skip_o_rules : unit -> ML bool

val get_json : unit -> ML bool
