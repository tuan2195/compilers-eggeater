open Printf
open Types
open Expr
open Instruction

type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
match e with
    | EPrim1(_, e, _) -> is_imm e
    | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
    | ELet(binds, body, _) -> List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
    | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
    | ETuple(expr_ls, _) -> List.for_all is_anf expr_ls
    | EGetItem(tup, idx, _) -> is_anf tup && is_imm idx
    | _ -> is_imm e
and is_imm e =
    match e with
    | ENumber _ -> true
    | EBool _ -> true
    | EId _ -> true
    | _ -> false
;;

let well_formed (p : (Lexing.position * Lexing.position) program) : exn list =
  let rec wf_E e (env : sourcespan envt) (funenv : (sourcespan * int) envt) =
    match e with
    | EBool _ -> []
    | ENumber(n, pos) ->
       if n > 1073741823 || n < -1073741824 then [Overflow(n, pos)] else []
    | EId (x, pos) ->
       (try ignore (List.assoc x env); []
        with Not_found -> [UnboundId(x, pos)])
    | EPrim1(_, e, _) -> wf_E e env funenv
    | EPrim2(_, l, r, _) -> wf_E l env funenv @ wf_E r env funenv
    | EIf(c, t, f, _) -> wf_E c env funenv @ wf_E t env funenv @ wf_E f env funenv
    | ELet(binds, body, _) ->
       let rec dupe x binds =
         match binds with
         | [] -> None
         | (y, _, pos)::_ when x = y -> Some pos
         | _::rest -> dupe x rest in
       let rec process_binds rem_binds env =
         match rem_binds with
         | [] -> (env, [])
         | (x, e, pos)::rest ->
            let shadow =
              match dupe x rest with
              | Some where -> [DuplicateId(x, where, pos)]
              | None ->
                 try
                   let existing = List.assoc x env in [ShadowId(x, pos, existing)]
                 with Not_found -> [] in
            let errs_e = wf_E e env funenv in
            let new_env = (x, pos)::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs_e @ errs)) in
       let (env2, errs) = process_binds binds env in
       errs @ wf_E body env2 funenv
    | EApp(funname, args, pos) ->
       (try let (_, arity) = (List.assoc funname funenv) in
            let actual = List.length args in
            if actual != arity then [Arity(arity, actual, pos)] else []
        with Not_found ->
          [UnboundFun(funname, pos)]) @ List.concat (List.map (fun e -> wf_E e env funenv) args)
    | EGetItem(tup, idx, _) ->
        wf_E tup env funenv  @ wf_E idx env funenv
       (* TODO: check if tuple is actually a tuple? you need to implement this *)
    | ETuple(expr_ls, _) ->
        List.flatten (List.map (fun e -> wf_E e env funenv) expr_ls)
       (* FILL: you need to implement this *)
  and wf_D d (env : sourcespan envt) (funenv : (sourcespan * int) envt) =
    match d with
    | DFun(_, args, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | (y, pos)::_ when x = y -> Some pos
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | (x, pos)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, pos)]) @ process_args rest in
       (process_args args) @ wf_E body (args @ env) funenv
  in
  match p with
  | Program(decls, body, _) ->
     let rec find name decls =
       match decls with
       | [] -> None
       | DFun(n, args, _, pos)::rest when n = name -> Some(pos)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, args, _, pos)::rest ->
          (match find name rest with
           | None -> []
           | Some where -> [DuplicateFun(name, where, pos)]) @ dupe_funbinds rest in
     let funbind d =
       match d with
       | DFun(name, args, _, pos) -> (name, (pos, List.length args)) in
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
        let (ans, setup) = help_foldI args in
        (CApp(funname, ans, ()), setup)
    | ETuple(expr_ls, _) ->
        let (ans, setup) = help_foldI expr_ls in
        (CTuple(ans, ()), setup)
        (*failwith "Implement ANF conversion for tuples"*)
    | EGetItem(tup, idx, _) ->
        let (tup_ans, tup_setup) = helpI tup in
        let (idx_ans, idx_setup) = helpI idx in
        (CGetItem(tup_ans, idx_ans, ()), tup_setup @ idx_setup)
       (*failwith "Implement ANF conversion for tuple-access"*)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)
  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | EPrim1(op, arg, tag) ->
        let name = sprintf "unary_%d" tag in
        let (arg_imm, arg_setup) = helpI arg in
        (ImmId(name, ()), arg_setup @ [(name, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
        let name = sprintf "binop_%d" tag in
        let (left_imm, left_setup) = helpI left in
        let (right_imm, right_setup) = helpI right in
        (ImmId(name, ()), left_setup @ right_setup @ [(name, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
        let name = sprintf "if_%d" tag in
        let (cond_imm, cond_setup) = helpI cond in
        (ImmId(name, ()), cond_setup @ [(name, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) ->
         let name = sprintf "func_%s_%d" funname tag in
         let (ans, setup) = helpC e in
         (ImmId(name, ()), setup @ [(name, ans)])
       (*failwith "Implement ANF conversion for function calls"*)
    | ETuple(expr_ls, tag) ->
         let name = sprintf "tuple_%d" tag in
         let (ans, setup) = helpC e in
         (ImmId(name, ()), setup @ [(name, ans)])
       (*failwith "Implement ANF conversion for tuples"*)
    | EGetItem(tup, idx, tag) ->
         let name = sprintf "getitem_%d" tag in
         let (ans, setup) = helpC e in
         (ImmId(name, ()), setup @ [(name, ans)])
       (*failwith "Implement ANF conversion for tuples"*)
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
        let (exp_ans, exp_setup) = helpC exp in
        let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  and help_foldI expr_ls = List.fold_left
    (fun (prev_ans, prev_setup) expr ->
        let (ans, setup) = helpI expr in
        (ans::prev_ans, setup @ prev_setup)
    )
    ([], [])
    expr_ls
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

(* Commonly used constants and macros *)
let const_true_value   = 0xFFFFFFFF
let const_true         = Sized(DWORD_PTR, HexConst(const_true_value))
let const_false_value  = 0x7FFFFFFF
let const_false        = Sized(DWORD_PTR, HexConst(const_false_value))
let bool_mask          = Sized(DWORD_PTR, HexConst(0x80000000))
let tag_as_bool        = Sized(DWORD_PTR, HexConst(0x00000007))

let err_COMP_NOT_NUM   = HexConst(1)
let err_ARITH_NOT_NUM  = HexConst(2)
let err_LOGIC_NOT_BOOL = HexConst(3)
let err_IF_NOT_BOOL    = HexConst(4)
let err_OVERFLOW       = HexConst(5)

let label_err_COMP_NOT_NUM   = "__err_COMP_NOT_NUM__"
let label_err_ARITH_NOT_NUM  = "__err_ARITH_NOT_NUM__"
let label_err_LOGIC_NOT_BOOL = "__err_LOGIC_NOT_BOOL__"
let label_err_IF_NOT_BOOL    = "__err_IF_NOT_BOOL__"
let label_err_OVERFLOW       = "__err_OVERFLOW__"

let label_func_begin name = sprintf "__%s_func_begin__" name
let label_true tag = sprintf "__true_%d__" tag
let label_false tag = sprintf "__false_%d__" tag
let label_done tag = sprintf "__done_%d__" tag
let label_else tag = sprintf "__else_%d__" tag
let label_end tag = sprintf "__end_%d__" tag

let rec arg_to_const arg =
    match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

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
    @ [ ILabel(label_func_begin fun_name); ]
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
(*and check_num err arg =*)
  (*[*)
    (*ITest(Sized(DWORD_PTR, arg), HexConst(0x00000001));*)
    (*IJnz(err)*)
  (*]*)
and check_num label arg =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IJmp(label); ]
        else
            []
    | _ ->
        [
            ITest(Sized(DWORD_PTR, arg), HexConst(0x00000001));
            IJnz(label)
        ]
and check_nums err left right = check_num err left @ check_num err right
and check_bool label scratch arg =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            []
        else
            [ IJmp(label); ]
    | _ ->
        (mov_if_needed scratch arg) @
        [
          IAnd(scratch, tag_as_bool);
          ICmp(scratch, tag_as_bool);
          IJne(label)
        ]
(*and check_bool err scratch arg =*)
    (*(mov_if_needed scratch arg) @*)
    (*[*)
      (*IAnd(scratch, HexConst(0x00000007));*)
      (*ICmp(scratch, HexConst(0x00000007));*)
      (*IJne(err)*)
    (*]*)
and check_bools err scratch left right = check_bool err scratch left @ check_bool err scratch right
and check_overflow err = [ IJo(err); ]
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
          @ (check_num label_err_ARITH_NOT_NUM (Reg EAX))
          @ [ IAdd(Reg(EAX), Const(2)) ]
          @ (check_overflow label_err_OVERFLOW)
       | Sub1 ->
          (mov_if_needed (Reg EAX) e_reg)
          @ (check_num label_err_ARITH_NOT_NUM (Reg EAX))
          @ [ IAdd(Reg(EAX), Const(~-2)) ]
          @ (check_overflow label_err_OVERFLOW)
       | IsBool | IsNum ->
          (mov_if_needed (Reg EAX) e_reg) @
            [
              IShl(Reg(EAX), Const(31));
              IOr(Reg(EAX), const_false)
            ]
       | IsTuple -> failwith "Not yet implemented: IsTuple"
       | Not ->
          (mov_if_needed (Reg EAX) e_reg)
          @ (check_bool label_err_LOGIC_NOT_BOOL (Reg EDX) (Reg EAX))
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
         @ check_nums label_err_ARITH_NOT_NUM (Reg EAX) (Reg EDX)
         @ [ op (Reg(EAX), Reg(EDX)) ]
         @ check_overflow label_err_OVERFLOW in
       let comp_op op =
         (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
         @ (check_nums label_err_COMP_NOT_NUM (Reg EAX) (Reg EDX))
         @ [
             (* More intuitive implementation *)
             ICmp(Reg(EAX), Reg(EDX));
             IMov(Reg(EAX), const_true);
             op (label_done tag);
             IMov(Reg(EAX), const_false);
             ILabel(label_done tag);
             (*IMov(Reg(EAX), left_reg);*)
             (*ICmp(Reg(EAX), right_reg);*)
             (*IMov(Reg(EAX), const_false);*)
             (*op (done_labe tag)l;*)
             (*IMov(Reg(EAX), const_true);*)
             (*ILabel(done_label tag);*)
           ] in
       let logic_op op =
         (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
         @ (check_bools label_err_LOGIC_NOT_BOOL (Reg ECX) (Reg EAX) (Reg EDX))
         @ [
             (*IMov(Reg(EAX), left_reg);*)
             op (Reg(EAX), Reg(EDX))
           ]  in
       begin match op with
       | Plus -> arith_op (fun (dest, src) -> IAdd(dest, src))
       | Minus -> arith_op (fun (dest, src) -> ISub(dest, src))
       | Times ->
          (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
          @ check_nums label_err_ARITH_NOT_NUM (Reg EAX) (Reg EDX)
          @ [ ISar(Reg(EAX), Const(1)); IMul(Reg(EAX), Reg(EDX)) ]
          @ check_overflow label_err_OVERFLOW
       | Less -> comp_op (fun dest -> IJl dest)
       | Greater -> comp_op (fun dest -> IJg dest)
       | LessEq -> comp_op (fun dest -> IJle dest)
       | GreaterEq -> comp_op (fun dest -> IJge dest)
       (*| Less -> comp_op (fun dest -> IJge dest)*)
       (*| Greater -> comp_op (fun dest -> IJle dest)*)
       (*| LessEq -> comp_op (fun dest -> IJg dest)*)
       (*| GreaterEq -> comp_op (fun dest -> IJl dest)*)
       | Eq ->
          (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
          @ (check_nums label_err_COMP_NOT_NUM (Reg EAX) (Reg EDX))
          @ [
              ICmp(Reg(EAX), Reg(EDX));
              IMov(Reg(EAX), const_true);
              IJe(label_done tag);
              IMov(Reg(EAX), const_false);
              ILabel(label_done tag)
            ]
       | And -> logic_op (fun (dest, src) -> IAnd(dest, src))
       | Or -> logic_op (fun (dest, src) -> IOr(dest, src))
       end
    | CIf(cond, thn, els, tag) ->
       let cond_reg = compile_imm cond env in
       (mov_if_needed (Reg EAX) cond_reg)
       @ (check_bool label_err_IF_NOT_BOOL (Reg ECX) (Reg EAX))
       @ [ ICmp(Reg(EAX), const_true); IJne(label_else tag) ]
       @ (compile_aexpr thn si env num_args is_tail)
       @ [ IJmp(label_end tag); ILabel(label_else tag) ]
       @ (compile_aexpr els si env num_args is_tail)
       @ [ ILabel(label_end tag) ]
    | CImmExpr i -> [ IMov(Reg(EAX), compile_imm i env) ]
    | CApp(name, args, _) ->
        if is_tail && (num_args = List.length args) then
           [   ILineComment(sprintf "Tail-call to function %s" name) ] @
              List.flatten (List.mapi
                  (fun i a -> [ IMov(Reg(EAX), a); IMov(RegOffset(word_size*(i+2), EBP), Reg(EAX)); ])
                  (List.rev_map (fun a -> compile_imm a env) args)) @
           [   IJmp(label_func_begin name) ]
        else
           call name (List.map (fun a -> compile_imm a env) args)
    | CTuple(expr_ls, _) ->
        let size = List.length expr_ls in
        let prelude = [
            IMov(Reg(EAX), Reg(ESI));
            IOr(Reg(EAX), HexConst(0x00000001));
            IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Const(size));
            IAdd(Reg(ESI), Const(word_size)); ] in
        let load = List.flatten( List.rev_map
            (fun a -> [
                IMov(Sized(DWORD_PTR, Reg(EDX)), compile_imm a env);
                IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Reg(EDX));
                IAdd(Reg(ESI), Const(word_size)); ] )
            expr_ls) in
        let padding =
            if size mod 2 = 0 then
                [ IInstrComment(IAdd(Reg(ESI), Const(word_size)), "Padding: size is even"); ]
            else [] in
        prelude @ load @ padding
       (* FILL: You need to implement this case *)
       (*failwith "not yet implemented: CTuple compilation"*)
    | CGetItem(tup, idx, _) -> [
        IMov(Sized(DWORD_PTR, Reg(EAX)), compile_imm tup env);
        ITest(Sized(DWORD_PTR, Reg(EAX)), HexConst(0x00000001));
        IJz(label_err_ARITH_NOT_NUM);
        ISub(Reg(EAX), Const(1));
        IMov(Sized(DWORD_PTR, Reg(ECX)), compile_imm idx env);
        (* TODO: check if number *)
        ISar(Reg(ECX), Const(1));
        IAdd(Reg(ECX), Const(1));
        IMov(Sized(DWORD_PTR, Reg(EDX)), RegOffset(0, EAX));
        ICmp(Reg(ECX), Reg(EDX));
        IJg(label_err_LOGIC_NOT_BOOL);
        IMov(Reg(EAX), RegOffsetReg(EAX, ECX, word_size, 0));
        ]




       (* FILL: You need to implement this case *)
       (*failwith "not yet implemented: CGetItem compilation"*)
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const(n lsl 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
and call label args =
  let setup = List.map (fun arg -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
    [ ILineComment(sprintf "Call to function %s" label) ] @ setup @ [ ICall(label) ] @ teardown
and optimize ls =
    match ls with
    | [] -> []
    | IMov(RegOffset(o1, b1), Reg(r1))::IMov(Reg(r2), RegOffset(o2, b2))::rest ->
        if o1 = o2 && b1 = b2 && r1 = r2 then
            (List.hd ls)::optimize rest
        else
            (List.nth ls 0)::(List.nth ls 1)::optimize rest
    | what::rest ->
        what::optimize rest
(*and optimize instrs = instrs*)
  (*match instrs with*)
  (*| IMov(Reg(EAX), exp)::IMov(dest, Reg(EAX))::tail -> IMov(Sized(DWORD_PTR, dest), exp)::optimize tail*)
  (*| i::tail -> i :: optimize tail*)
  (*| [] -> []*)
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
%s:%s
%s:%s
%s:%s
%s:%s
%s:%s"
   label_err_COMP_NOT_NUM   (to_asm (call "error" [err_COMP_NOT_NUM]))
   label_err_ARITH_NOT_NUM  (to_asm (call "error" [err_ARITH_NOT_NUM]))
   label_err_LOGIC_NOT_BOOL (to_asm (call "error" [err_LOGIC_NOT_BOOL]))
   label_err_IF_NOT_BOOL    (to_asm (call "error" [err_IF_NOT_BOOL]))
   label_err_OVERFLOW       (to_asm (call "error" [err_OVERFLOW]))
  in
  match anfed with
  | AProgram(decls, body, _) ->
     let comp_decls = List.map compile_decl decls in

     let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" [] body in
     let heap_start = [
         ILineComment("heap start");
         (*IInstrComment(IMov(Reg(ESI), RegOffset(4, ESP)), "Load ESI with our argument, the heap pointer");*)
         IInstrComment(IMov(Reg(ESI), RegOffset(8, EBP)), "Load ESI with our argument, the heap pointer");
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

