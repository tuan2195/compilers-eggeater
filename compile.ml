open Printf
open Types
open Expr
open Instruction

type 'a envt = (string * 'a) list

                             
let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  (* fill in other cases here *)
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;


let const_true = HexConst (0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask = HexConst(0x80000000)

let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5

                           
let well_formed (p : (Lexing.position * Lexing.position) program) : exn list =
  let rec wf_E e (env : sourcespan envt) (funenv : (sourcespan * int) envt) =
    match e with
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > 1073741823 || n < -1073741824 then [Overflow(n, loc)] else []
    | EId (x, loc) ->
       (try ignore (List.assoc x env); []
        with Not_found -> [UnboundId(x, loc)])
    | EPrim1(_, e, _) -> wf_E e env funenv
    | EPrim2(_, l, r, _) -> wf_E l env funenv @ wf_E r env funenv
    | EIf(c, t, f, _) -> wf_E c env funenv @ wf_E t env funenv @ wf_E f env funenv
    | ELet(binds, body, _) ->
       let rec dupe x binds =
         match binds with
         | [] -> None
         | (y, _, loc)::_ when x = y -> Some loc
         | _::rest -> dupe x rest in
       let rec process_binds rem_binds env =
         match rem_binds with
         | [] -> (env, [])
         | (x, e, loc)::rest ->
            let shadow =
              match dupe x rest with
              | Some where -> [DuplicateId(x, where, loc)]
              | None ->
                 try
                   let existing = List.assoc x env in [ShadowId(x, loc, existing)]
                 with Not_found -> [] in
            let errs_e = wf_E e env funenv in
            let new_env = (x, loc)::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs_e @ errs)) in              
       let (env2, errs) = process_binds binds env in
       errs @ wf_E body env2 funenv
    | EApp(funname, args, loc) ->
       (try let (_, arity) = (List.assoc funname funenv) in
            let actual = List.length args in
            if actual != arity then [Arity(arity, actual, loc)] else []
        with Not_found ->
          [UnboundFun(funname, loc)]) @ List.concat (List.map (fun e -> wf_E e env funenv) args)
    | EGetItem(l, r, _) ->
       (* FILL: you need to implement this *)
       failwith "not yet implemented: getitem well-formedness"
    | ETuple(elts, _) ->
       (* FILL: you need to implement this *)
       failwith "not yet implemented: tuple well-formedness"
  and wf_D d (env : sourcespan envt) (funenv : (sourcespan * int) envt) =
    match d with
    | DFun(_, args, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | (y, loc)::_ when x = y -> Some loc
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | (x, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest in
       (process_args args) @ wf_E body (args @ env) funenv
  in
  match p with
  | Program(decls, body, _) ->
     let rec find name decls =
       match decls with
       | [] -> None
       | DFun(n, args, _, loc)::rest when n = name -> Some(loc)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, args, _, loc)::rest ->
          (match find name rest with
           | None -> []
           | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
     let funbind d =
       match d with
       | DFun(name, args, _, loc) -> (name, (loc, List.length args)) in
     let funbinds : (string * (sourcespan * int)) list = List.map funbind decls in
     (dupe_funbinds decls)
     @ (List.concat (List.map (fun d -> wf_D d [] funbinds) decls))
     @ (wf_E body [] funbinds)
;;


let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) -> ADFun(name, List.map fst args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EApp(funname, args, _) ->
       failwith "Implement ANF conversion for function calls"
    | ETuple(vals, _) ->
       failwith "Implement ANF conversion for tuples"
    | EGetItem(tup, idx, _) ->
       failwith "Implement ANF conversion for tuple-access"
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) ->
       failwith "Implement ANF conversion for function calls"
    | ETuple(vals, _) ->
       failwith "Implement ANF conversion for tuples"
    | EGetItem(tup, idx, _) ->
       failwith "Implement ANF conversion for tuple-access"
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;


  
  

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

let rec compile_fun fun_name args e : (instruction list * instruction list * instruction list) =
  let args_env = List.mapi (fun i a -> (a, RegOffset(word_size * (i + 2), EBP))) args in
  let compiled = (compile_aexpr e 1 args_env (List.length args) true) in
  let count_local_vars = count_vars e in
  let optimized = optimize compiled in
  (([
       ILabel(fun_name);
       ILineComment("Function prologue");
       IPush(Reg(EBP));
       IMov(Reg(EBP), Reg(ESP))
     ]
    @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars),
   ([ ILineComment("Function body") ]
    @ optimized),
   [
     ILineComment("Function epilogue");
     IMov(Reg(ESP), Reg(EBP));
     IPop(Reg(EBP));
     IInstrComment(IRet, sprintf "End of %s" fun_name)
  ])
and mov_if_needed dest src =
  if dest = src then []
  else [ IMov(dest, src) ]
and check_num err arg =
  [
    ITest(Sized(DWORD_PTR, arg), HexConst(0x00000001));
    IJnz(err)
  ]
and check_nums err left right = check_num err left @ check_num err right
and check_bool err scratch arg =
  (mov_if_needed scratch arg) @
    [
      IAnd(scratch, HexConst(0x00000007));
      ICmp(scratch, HexConst(0x00000007));
      IJne(err)    
    ]
and check_bools err scratch left right = check_bool err scratch left @ check_bool err scratch right
and check_overflow err =
  [
    IJo(err);
  ]
and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, e, body, _) ->
     let prelude = compile_cexpr e (si + 1) env num_args false in
     let body = compile_aexpr body (si + 1) ((id, RegOffset(~-word_size * si, EBP))::env) num_args is_tail in
     prelude
     @ [ IMov(RegOffset(~-word_size * si, EBP), Reg(EAX)) ]
     @ body
  | ACExpr e -> compile_cexpr e si env num_args is_tail
and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  match e with
  | CPrim1(op, e, tag) ->
     let e_reg = compile_imm e env in
     begin match op with
     | Add1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(2)) ]
        @ (check_overflow "err_overflow")
     | Sub1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(~-2)) ]
        @ (check_overflow "err_overflow")
     | IsBool | IsNum ->
        (mov_if_needed (Reg EAX) e_reg) @
          [
            IShl(Reg(EAX), Const(31));
            IOr(Reg(EAX), const_false)
          ]
     | IsTuple -> failwith "Not yet implemented: IsTuple"
     | Not ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_bool "err_logic_not_bool" (Reg EDX) (Reg EAX))
        @ [ IXor(Reg(EAX), bool_mask) ]
     | Print ->
        (mov_if_needed (Reg EAX) e_reg)
        @ call "print" [Sized(DWORD_PTR, Reg EAX)]
     | PrintStack ->
        (mov_if_needed (Reg EAX) e_reg)
        @ call "print_stack"
               [Sized(DWORD_PTR, Reg(EAX));
                Sized(DWORD_PTR, Reg(ESP));
                Sized(DWORD_PTR, Reg(EBP));
                Sized(DWORD_PTR, Const(num_args))]
     end
  | CPrim2(op, left, right, tag) ->
     let left_reg = compile_imm left env in
     let right_reg = compile_imm right env in
     let arith_op op =
       (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
       @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
       @ [ op (Reg(EAX), Reg(EDX)) ]
       @ check_overflow "err_overflow" in
     let comp_op op =
       let true_label = sprintf "true_%d" tag in
       let done_label = sprintf "done_%d" tag in
       (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
       @ (check_nums "err_comp_not_num" (Reg EAX) (Reg EDX))
       @ [
           IMov(Reg(EAX), left_reg);
           ICmp(Reg(EAX), right_reg);
           IMov(Reg(EAX), const_false);
           op done_label;
           ILabel(true_label);
           IMov(Reg(EAX), const_true);
           ILabel(done_label);
         ] in
     let logic_op op =
       (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
       @ (check_bools "err_arith_not_num" (Reg ECX) (Reg EAX) (Reg EDX))
       @ [
           IMov(Reg(EAX), left_reg);
           op (Reg(EAX), right_reg)
         ]  in
     begin match op with
     | Plus -> arith_op (fun (dest, src) -> IAdd(dest, src))
     | Minus -> arith_op (fun (dest, src) -> ISub(dest, src))
     | Times ->
        (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
        @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
        @ [ ISar(Reg(EAX), Const(1)); IMul(Reg(EAX), Reg(EDX)) ]
        @ check_overflow "err_overflow"
     | Less -> comp_op (fun dest -> IJge dest)
     (* You're encouraged to try generating better code for these comparisons.
           The following code should work for lessthan; generate similar code for the others *)
     (* [
         IMov(Reg(EAX), left_reg);
         ISar(Reg(EAX), Const(1));
         IMov(Reg(EBX), right_reg);
         ISar(Reg(EBX), Const(1));
         ISub(Reg(EAX), Reg(EBX));
         IAnd(Reg(EAX), bool_mask);
         IOr(Reg(EAX), tag_as_bool)
       ] *)
     | Greater -> comp_op (fun dest -> IJle dest)
     | LessEq -> comp_op (fun dest -> IJg dest)
     | GreaterEq -> comp_op (fun dest -> IJl dest)
     | Eq ->
        let true_label = sprintf "true_%d" tag in
        let done_label = sprintf "done_%d" tag in
        (mov_if_needed (Reg EAX) left_reg) @
          [
            ICmp(Reg(EAX), right_reg);
            IMov(Reg(EAX), const_false);
            IJne(done_label);
            ILabel(true_label);
            IMov(Reg(EAX), const_true);
            ILabel(done_label)
          ]
     | And -> logic_op (fun (dest, src) -> IAnd(dest, src))
     | Or -> logic_op (fun (dest, src) -> IOr(dest, src))
     end
  | CIf(cond, thn, els, tag) ->
     let cond_reg = compile_imm cond env in
     let else_label = sprintf "else_%d" tag in
     let end_label = sprintf "end_%d" tag in
     (mov_if_needed (Reg EAX) cond_reg)
     @ (check_bool "err_if_not_bool" (Reg ECX) (Reg EAX))
     @ [      
         ICmp(Reg(EAX), const_true);
         IJne(else_label)
       ]
     @ (compile_aexpr thn si env num_args is_tail)
     @ [ IJmp(end_label); ILabel(else_label) ]
     @ (compile_aexpr els si env num_args is_tail)
     @ [ ILabel(end_label) ]
  | CImmExpr i -> [ IMov(Reg(EAX), compile_imm i env) ]
  | CApp(funname, args, _) ->
     (* This implementation ignores tail calls entirely.  Please fix it. *)
     let numargs = List.length args in
     let pushargs = List.rev (List.map (fun a -> IPush (Sized(DWORD_PTR, compile_imm a env))) args) in
     pushargs
     @ [ ICall(funname); IAdd(Reg(ESP), HexConst(4*numargs)) ]
  | CTuple(elts, _) ->
     (* FILL: You need to implement this case *)
     failwith "not yet implemented: CTuple compilation"
  | CGetItem(coll, index, _) ->
     (* FILL: You need to implement this case *)
     failwith "not yet implemented: CGetItem compilation"
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const((n lsl 1))
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
and call label args =
  let setup = List.rev_map (fun arg -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(label) ] @ teardown
and optimize instrs =
  match instrs with
  | IMov(Reg(EAX), exp)::IMov(dest, Reg(EAX))::tail -> IMov(Sized(DWORD_PTR, dest), exp)::optimize tail
  | i::tail -> i :: optimize tail
  | [] -> [] 
;;
  
let compile_decl (d : tag adecl) : instruction list =
  match d with
  | ADFun(name, args, body, _) ->
     let (prologue, comp_body, epilogue) = compile_fun name args body
     in (prologue @ comp_body @ epilogue)
;;



let compile_prog anfed =
  let prelude =
    "section .text
extern error
extern print
extern print_stack
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_overflow:%s"
                       (to_asm (call "error" [Const(err_COMP_NOT_NUM)]))
                       (to_asm (call "error" [Const(err_ARITH_NOT_NUM)]))
                       (to_asm (call "error" [Const(err_LOGIC_NOT_BOOL)]))
                       (to_asm (call "error" [Const(err_IF_NOT_BOOL)]))
                       (to_asm (call "error" [Const(err_OVERFLOW)]))
  in
  match anfed with
  | AProgram(decls, body, _) ->
     let comp_decls = List.map compile_decl decls in

     let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" [] body in
     let heap_start = [
         ILineComment("heap start");
         IInstrComment(IMov(Reg(ESI), RegOffset(4, ESP)), "Load ESI with our argument, the heap pointer");
         IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
         IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
       ] in
     let main = (prologue @ heap_start @ comp_main @ epilogue) in
     
     let as_assembly_string = ExtString.String.join "\n" (List.map to_asm comp_decls) in
     sprintf "%s%s\n%s%s\n" prelude as_assembly_string (to_asm main) suffix



let compile_to_string prog : (exn list, string) either =
  let errors = well_formed prog in
  match errors with
  | [] ->
     let tagged : tag program = tag prog in
     let anfed : tag aprogram = atag (anf tagged) in
     (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
     (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
     (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
     Right(compile_prog anfed)
  | _ -> Left(errors)

