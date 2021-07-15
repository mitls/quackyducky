%{
  open FStar_Pervasives
  open Lexing
  open Ast
  let mk_td b i j k = {
    typedef_name = i;
    typedef_abbrev = j;
    typedef_ptr_abbrev = k;
    typedef_attributes = b
  }

  let mk_pos (l:Lexing.position) =
      let col = (l.pos_cnum - l.pos_bol + 1) in
      {
        filename=l.pos_fname;
        line=Z.of_int l.pos_lnum;
        col=Z.of_int col;
      }

  let with_range (x:'a) (l:Lexing.position) : 'a with_meta_t =
      Ast.with_range x (mk_pos l, mk_pos l)

  let pointer_name j p =
      match p with
      | None -> {j with v={j.v with name="P"^j.v.name}}
      | Some k -> k

  let parse_int_and_type r (s:string) : Z.t * string * integer_type =
      let r = mk_pos r, mk_pos r in
      let s', t = parse_int_suffix s in
      let i = Z.of_string s' in
      let t' = smallest_integer_type_of r i in
      let t = match t with
              | None -> t'
              | Some t ->
                if integer_type_leq t' t
                then t
                else error ("Integer " ^s^ " is too large for the specified type") r
      in
      i, s', t
%}

%token<string>  INT XINT STRING
%token<string>  BLOCK_COMMENT
%token<bool>    BOOL
%token<Ast.ident> IDENT
%token          EQ DOUBLEEQ NEQ AND OR NOT EOF SIZEOF ENUM TYPEDEF STRUCT CASETYPE SWITCH CASE DEFAULT THIS
%token          DEFINE LPAREN RPAREN LBRACE RBRACE DOT COMMA SEMICOLON COLON QUESTION
%token          STAR DIV MINUS PLUS LEQ LESS_THAN GEQ GREATER_THAN WHERE REQUIRES IF ELSE
%token          LBRACK RBRACK LBRACK_LEQ LBRACK_EQ LBRACK_BYTESIZE LBRACK_BYTESIZE_AT_MOST LBRACK_SINGLE_ELEMENT_BYTESIZE
%token          LBRACK_STRING LBRACK_STRING_AT_MOST
%token          MUTABLE LBRACE_ONSUCCESS FIELD_POS FIELD_PTR VAR ABORT RETURN
%token          REM SHIFT_LEFT SHIFT_RIGHT BITWISE_AND BITWISE_OR BITWISE_XOR BITWISE_NOT AS
%token          MODULE EXPORT
%token          ENTRYPOINT REFINING ALIGNED
(* LBRACE_ONERROR CHECK  *)
%start <Ast.prog> prog
%start <Ast.expr> expr_top

%left OR
%left AND
%left BITWISE_OR
%left BITWISE_XOR
%left BITWISE_AND
%nonassoc NEQ DOUBLEEQ
%nonassoc LEQ LESS_THAN GEQ GREATER_THAN
%left SHIFT_LEFT SHIFT_RIGHT
%left PLUS MINUS
%left STAR REM DIV
%nonassoc BITWISE_NOT NOT

%%

option_of (X):
  |  { None }
  | x=X { Some x }

right_flexible_list(SEP, X):
  |     { [] }
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

right_flexible_nonempty_list(SEP, X):
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

constant:
  | i=INT    { let n, _, t = parse_int_and_type ($startpos(i)) i in Int(t, n) }
  | i=XINT   { let _, x, t = parse_int_and_type ($startpos(i)) i in XInt(t, x) }
  | b=BOOL   { Bool b }

rel_op:
  | DOUBLEEQ     { Eq }
  | NEQ          { Neq }
  | LEQ          { LE None }
  | LESS_THAN    { LT None }
  | GEQ          { GE None }
  | GREATER_THAN { GT None }

else_opt:
  |             { None   }
  | ELSE LBRACE e=expr RBRACE { Some e }

atomic_expr:
  | i=qident   { Identifier i }
  | THIS       { This }
  | c=constant { Constant c }

atomic_or_paren_expr:
  | e=atomic_expr  { with_range e $startpos }
  | LPAREN e=expr RPAREN { e }

castable_expr:
  |               { None }
  | e=atomic_expr { Some e }
  | LPAREN e=expr RPAREN { Some e.v }

expr_no_range:
  | e=atomic_expr { e }
  | LPAREN e=expr RPAREN eopt=castable_expr {
      match e, eopt with
      | _, None -> e.v
      | {v=Identifier i}, Some e' ->
        let e' = with_range e' $startpos(eopt) in
        App (Cast (None, as_integer_typ i), [e'])
      | _ ->
        error ("Expected a cast expression, got " ^ (print_expr e)) e.range
    }
  | l=expr o=rel_op r=expr %prec DOUBLEEQ
    { App (o, [l;r]) }
  | l=expr AND r=expr
    { App (And, [l;r]) }
  | l=expr OR r=expr
    { App (Or, [l;r]) }
  | l=expr MINUS r=expr
    { App (Minus None, [l;r]) }
  | l=expr PLUS r=expr
    { App (Plus None, [l;r]) }
  | l=expr STAR r=expr
    { App (Mul None, [l;r]) }
  | l=expr DIV r=expr
    { App (Division None, [l;r]) }
  | l=expr REM r=expr
    { App (Remainder None, [l;r]) }
  | l=expr BITWISE_AND r=expr
    { App (BitwiseAnd None, [l;r]) }
  | l=expr BITWISE_XOR r=expr
    { App (BitwiseXor None, [l;r]) }
  | l=expr BITWISE_OR r=expr
    { App (BitwiseOr None, [l;r]) }
  | BITWISE_NOT l=expr
    { App (BitwiseNot None, [l]) }
  | l=expr SHIFT_RIGHT r=expr
    { App (ShiftRight None, [l;r]) }
  | l=expr SHIFT_LEFT r=expr
    { App (ShiftLeft None, [l;r]) }
  | NOT e=expr
    { App (Not, [e]) }
  | SIZEOF LPAREN e=expr RPAREN
    { App (SizeOf, [e]) }
  | e=atomic_or_paren_expr QUESTION e1=atomic_or_paren_expr COLON e2=atomic_or_paren_expr
    {
        App(IfThenElse, [e;e1;e2])
    }
  | IF e=expr LBRACE e1=expr RBRACE e2=else_opt
    {
        let e2 =
            match e2 with
            | None -> with_range (Constant (Bool true)) $startpos
            | Some e2 -> e2
        in
        App(IfThenElse, [e;e1;e2])
    }
  | i=IDENT LPAREN es=arguments RPAREN
    {
       App(Ext i.v.name, es)
    }

expr:
  | e=expr_no_range { with_range e $startpos }

arguments:
 | es=right_flexible_nonempty_list(COMMA, expr)  { es }

qident:
  | i=IDENT    { i }
  | m=IDENT DOT n=IDENT    { with_range ({modul_name=Some m.v.name; name=n.v.name}) $startpos }

typ_no_range:
  | i=qident { Type_app(i, []) }
  | hd=qident LPAREN a=arguments RPAREN { Type_app(hd, a) }

typ:
  | t=typ_no_range { with_range t $startpos }

maybe_pointer_typ:
  | t=typ { t }
  | t=pointer_typ { t }

pointer_typ:
  | t=maybe_pointer_typ STAR { with_range (Pointer t) $startpos }

refinement:
  | LBRACE e=expr RBRACE { e }

array_size:
  | LBRACK e=expr RBRACK                         { (e, ByteArrayByteSize) }
  | LBRACK_BYTESIZE e=expr RBRACK                { (e, ArrayByteSize) }
  | LBRACK_LEQ e=expr RBRACK                     { (e, ArrayByteSizeAtMost) }
  | LBRACK_BYTESIZE_AT_MOST e=expr RBRACK        { (e, ArrayByteSizeAtMost) }
  | LBRACK_EQ e=expr RBRACK                      { (e, ArrayByteSizeSingleElementArray) }
  | LBRACK_SINGLE_ELEMENT_BYTESIZE e=expr RBRACK { (e, ArrayByteSizeSingleElementArray) }

array_annot:
  | { FieldScalar }
  | a=array_size { FieldArrayQualified a }
  | LBRACK_STRING RBRACK { FieldString None }
  | LBRACK_STRING_AT_MOST e=expr RBRACK { FieldString (Some e) }

bitwidth:
  | COLON i=INT { Inl (with_range (Z.of_string i) $startpos(i)) }

field_action:
  | LBRACE_ONSUCCESS a=action RBRACE { a, false }

struct_field:
  | t=typ fn=IDENT bopt=option_of(bitwidth) aopt=array_annot c=option_of(refinement) a=option_of(field_action)
    {
        {
         field_dependence=false;
         field_ident=fn;
         field_type=t;
         field_array_opt=aopt;
         field_constraint=c;
         field_bitwidth=bopt;
         field_action=a
        }
    }

field:
  | f = struct_field
    {
      let comms = Ast.comments_buffer.flush () in
      let range = (mk_pos $startpos, mk_pos $startpos) in
      with_range_and_comments f range comms
    }


immutable_parameter:
  | t=typ i=IDENT { (t, i, Immutable) }

mutable_parameter:
  | MUTABLE t=pointer_typ i=IDENT { (t, i, Mutable) }

parameter:
  | i=immutable_parameter { i }
  | m=mutable_parameter { m }

parameters:
  |  { [] }
  | LPAREN ps=right_flexible_nonempty_list(COMMA, parameter) RPAREN { ps }

case_pattern:
  | i=qident   { with_range (Identifier i) $startpos(i) }
  | c=constant { with_range (Constant c) $startpos(c) }

case:
  | CASE p=case_pattern COLON f=field { Case (p, f) }
  | DEFAULT COLON f=field { DefaultCase f }

cases:
  | cs=right_flexible_nonempty_list(SEMICOLON, case) { cs }

attribute:
  | ENTRYPOINT { Entrypoint }
  | ALIGNED    { Aligned }

attributes:
  |            { [] }
  | a=attribute tl=attributes { a :: tl }

where_opt:
  |              { None }
  | WHERE e=expr { Some e }
  | REQUIRES e=expr { Some e }

atomic_action:
  | RETURN e=expr SEMICOLON { Action_return e }
  | ABORT SEMICOLON         { Action_abort }
  | FIELD_POS SEMICOLON     { Action_field_pos }
  | FIELD_PTR SEMICOLON     { Action_field_ptr }
  | STAR i=IDENT SEMICOLON  { Action_deref i }
  | STAR i=IDENT EQ e=expr SEMICOLON { Action_assignment(i, e) }
  | f=IDENT LPAREN args=arguments RPAREN SEMICOLON { Action_call(f, args) }

action_else:
  | ELSE LBRACE a=action RBRACE { a }

action_no_range:
  | a=atomic_action { Atomic_action a }
  | a1=atomic_action a=action { Action_seq (a1, a) }
  | IF e=expr LBRACE a1=action RBRACE a2=option_of(action_else) { Action_ite (e, a1, a2) }
  | VAR i=IDENT EQ a1=atomic_action a2=action               { Action_let (i, a1, a2) }

action:
  | a=action_no_range { with_range a ($startpos(a)) }

enum_case:
  | i=IDENT            { i, None }
  | i=IDENT EQ j=INT   { i, Some (Inl (Z.of_string j)) }
  | i=IDENT EQ j=IDENT { i, Some (Inr j) }

exported:
  |              { false }
  | EXPORT       { true }

maybe_semi:
  |           { () }
  | SEMICOLON { () }

typedef_pointer_name_opt:
  |                    { None }
  | COMMA STAR k=IDENT { Some k }

decl_no_range:
  | MODULE i=IDENT EQ m=IDENT { ModuleAbbrev (i, m) }
  | DEFINE i=IDENT c=constant { Define (i, None, c) }
  | t=IDENT ENUM i=IDENT LBRACE es=right_flexible_nonempty_list(COMMA, enum_case) RBRACE maybe_semi
    { Enum(with_range (Type_app (t, [])) ($startpos(t)), i, es) }
  | b=attributes TYPEDEF t=typ i=IDENT SEMICOLON
    { TypeAbbrev (t, i) }
  | b=attributes TYPEDEF STRUCT i=IDENT ps=parameters w=where_opt
    LBRACE fields=right_flexible_nonempty_list(SEMICOLON, field)
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {  let k = pointer_name j p in
       Record(mk_td b i j k, ps, w, fields)
    }
  | b=attributes CASETYPE i=IDENT ps=parameters
    LBRACE SWITCH LPAREN e=IDENT RPAREN
           LBRACE cs=cases
           RBRACE
    RBRACE j=IDENT p=typedef_pointer_name_opt SEMICOLON
    {
        let k = pointer_name j p in
        let td = mk_td b i j k in
        CaseType(td, ps, (with_range (Identifier e) ($startpos(i)), cs))
    }

block_comment_opt:
  |                 { None }
  | c=BLOCK_COMMENT { Some c }

decl:
  | c=block_comment_opt isexported=exported d=decl_no_range {
      let _ = Ast.comments_buffer.flush () in
      let r = mk_pos ($startpos(d)), mk_pos ($startpos(d)) in
      match c with
      | Some c -> mk_decl d r [c] isexported
      | None -> mk_decl d r [] isexported
    }

expr_top:
  | e=expr EOF { e }

type_map:
  | i=IDENT { i, None }
  | i=IDENT AS j=IDENT { i, Some j }

type_refinement:
  | REFINING includes=right_flexible_nonempty_list(COMMA, STRING)
    LBRACE
      type_map=right_flexible_nonempty_list(COMMA, type_map)
    RBRACE
    {
          {
            includes = includes;
            type_map = type_map
          }
    }

prog:
  | d=decl r=option_of(type_refinement) EOF
    { [d], r }
  | d=decl p=prog
    {
        let tl, r = p in
        (d :: tl), r
    }
