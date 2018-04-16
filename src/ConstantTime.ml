module A = Ast
module WA = Wasm.Ast
module WS = Wasm.Source
module WV = Wasm.Values
module WT = Wasm.Types
module WU = Wasm.Utf8
module L = Location

type secrecy =
  | Secret
  | Public
  | Zero

let show_secrecy secrecy = match secrecy with
  | Secret -> "S"
  | Public -> "P"
  | Zero -> "Z"

type proto_secrecy = secrecy list * secrecy * A.ident

module IdentMap = Map.Make (struct
    type t = A.ident
    let compare = compare
  end)

type secrecy_data = proto_secrecy list IdentMap.t

module LocalMap = Map.Make (struct
    type t = int32
    let compare = compare
  end)

type value_stack = secrecy Stack.t

let decl_typ_ident (decl : A.decl) : (A.lident * A.typ list * A.typ) option =
  match decl with
  | A.DFunction (_,_,_,typ,lident,binders,_) ->
    Some(lident, List.map (fun binder -> binder.Ast.typ) binders,typ)
  | A.DGlobal _
  | A.DType _
  | A.DExternal _-> None

let typ_to_secret (typ: A.typ) : secrecy = match typ with
  | A.TInt _ | A.TBool | A.TUnit | A.TAny
  | A.TBuf _ | A.TArray _ ->
    Public
  | A.TQualified _ | A.TArrow _ | A.TApp _ | A.TBound _
  | A.TTuple _ | A.TAnonymous _ ->
    assert false


let analyse_function_prototype_secrecy (files : A.file list) : secrecy_data =
  let secrecy = List.fold_left (fun secrecy_data (filename,program) ->
      List.fold_left (fun secrecy_data decl ->
          match decl_typ_ident decl with
          | None -> secrecy_data
          | Some ((_,ident),typ_args,typ) ->
            try
              let funcs_secrecy = IdentMap.find filename secrecy_data in
              IdentMap.add filename
                ((List.map typ_to_secret typ_args,
                  typ_to_secret typ, ident)::funcs_secrecy)
                secrecy_data
            with
            | Not_found ->
              IdentMap.add filename
                [List.map typ_to_secret typ_args, typ_to_secret typ, ident]
                secrecy_data
        ) secrecy_data program
    ) IdentMap.empty files
  in
  IdentMap.map (fun proto_list -> List.rev proto_list) secrecy

type loc = L.loc list

let assert_public (arg : secrecy) (err_context : string) (loc: loc) : unit =
  match arg with
  | Public | Zero -> ()
  | Secret ->
    Warnings.maybe_fatal_error
      (KPrint.bsprintf "%a" L.ploc loc, Warnings.ConstantTimeValidatorFailure (
          err_context,
          "the value should be public but it is secret"
        ))

let set_local
    (var : int32)
    (locals_secrecy : secrecy LocalMap.t)
    (secrecy : secrecy)
    (loc : loc)
  : secrecy LocalMap.t =
  try
    let previous_secrecy = LocalMap.find var locals_secrecy in
    if previous_secrecy = Public then
      assert_public secrecy ("value assigned to a public local variable") loc;
    locals_secrecy
  with
  | Not_found ->
    LocalMap.add var secrecy locals_secrecy

let constant_time_binop (op : WA.binop) : bool = match op with
  | WV.I32 (WA.I32Op.Add)
  | WV.I32 (WA.I32Op.And)
  | WV.I32 (WA.I32Op.Sub)
  | WV.I32 (WA.I32Op.Mul)
  | WV.I32 (WA.I32Op.Xor)
  | WV.I32 (WA.I32Op.Or)
  | WV.I32 (WA.I32Op.Rotl)
  | WV.I32 (WA.I32Op.Rotr)
  | WV.I32 (WA.I32Op.Shl)
  | WV.I32 (WA.I32Op.ShrS)
  | WV.I32 (WA.I32Op.ShrU)
  | WV.I64 (WA.I64Op.Add)
  | WV.I64 (WA.I64Op.And)
  | WV.I64 (WA.I64Op.Sub)
  | WV.I64 (WA.I64Op.Mul)
  | WV.I64 (WA.I64Op.Xor)
  | WV.I64 (WA.I64Op.Or)
  | WV.I64 (WA.I64Op.Rotl)
  | WV.I64 (WA.I64Op.Rotr)
  | WV.I64 (WA.I64Op.Shl)
  | WV.I64 (WA.I64Op.ShrS)
  | WV.I64 (WA.I64Op.ShrU)
    -> true
  | _ -> false

let constant_time_unop (_ : WA.unop) : bool = false

let unify_unop_ct (arg : secrecy) : secrecy = arg

let unify_unop_vt (arg : secrecy) (loc : loc) : secrecy =
  assert_public arg "argument of a variable-time unary operator" loc;
  Public

let unify_ct_binop (arg1 : secrecy) (arg2: secrecy) : secrecy =
  match arg1, arg2 with
  | (Public, Public) -> Public
  | (Zero, Zero) -> Public
  | (Public, Zero) | (Zero, Public) -> Public
  | (Secret, Public) | (Public, Secret)
  | (Secret, Zero) | (Zero, Secret)
  | (Secret, Secret) -> Secret

let unify_vt_binop (arg1 : secrecy) (arg2 : secrecy) (loc : loc) : secrecy =
  assert_public arg1 "first argument of a variable-time binary operator" loc;
  assert_public arg2 "second argument of a variable-time binary operator" loc;
  Public


let rec check_instrs (wasm_func_secrecy : proto_secrecy list)
    (locals_secrecy : secrecy LocalMap.t)
    (value_stack : secrecy Stack.t)
    (func_result : secrecy)
    (instrs: WA.instr list)
    (loc : loc)
  : secrecy LocalMap.t * secrecy Stack.t =
  List.fold_left (fun (locals_secrecy, value_stack) instr ->
      check_instr
        wasm_func_secrecy
        locals_secrecy
        value_stack
        func_result
        instr
        loc
    ) (locals_secrecy, value_stack) instrs

and check_instr
    (wasm_func_secrecy : proto_secrecy list)
    (locals_secrecy : secrecy LocalMap.t)
    (value_stack : secrecy Stack.t)
    (func_result: secrecy)
    (instr: WA.instr)
    (loc : loc)
  : secrecy LocalMap.t * secrecy Stack.t =
  match instr.WS.it with
  | WA.Unreachable | WA.Nop | WA.Br _ | WA.BrIf _ | WA.BrTable _ ->
    locals_secrecy, value_stack
  | WA.GetLocal var ->
    Stack.push (LocalMap.find var.WS.it locals_secrecy) value_stack;
    locals_secrecy, value_stack
  | WA.SetLocal var ->
    let arg_secret = Stack.pop value_stack in
    set_local var.WS.it locals_secrecy arg_secret loc, value_stack
  | WA.GetGlobal _ ->
    Stack.push Public value_stack;
    locals_secrecy, value_stack
  | WA.SetGlobal _ ->
    let arg_secret = Stack.pop value_stack in
    assert_public arg_secret "value assigned to a global variable" loc;
    locals_secrecy, value_stack
  | WA.Load _ ->
    let address = Stack.pop value_stack in
    assert_public address "address for a memory load" loc;
    begin match address with
      | Zero ->  Stack.push Public value_stack
      | Public ->   Stack.push Secret value_stack;
      | Secret -> assert false
    end;
    locals_secrecy, value_stack
  | WA.Store _ ->
    let _ = Stack.pop value_stack in
    let address = Stack.pop value_stack in
    assert_public address "Address for a memory store" loc;
    locals_secrecy, value_stack
  | WA.Const v when v.WS.it = WV.I32 (Int32.zero)  ->
    Stack.push Zero value_stack;
    locals_secrecy, value_stack
  | WA.Const _ ->
    Stack.push Public value_stack;
    locals_secrecy, value_stack
  | WA.Binary op ->
    let arg1 = Stack.pop value_stack in
    let arg2 = Stack.pop value_stack in
    let result = if constant_time_binop op then
        unify_ct_binop arg1 arg2
      else
        unify_vt_binop arg1 arg2 loc
    in
    Stack.push result value_stack;
    locals_secrecy, value_stack
  | WA.Compare _ ->
    let arg1 = Stack.pop value_stack in
    let arg2 = Stack.pop value_stack in
    let result = unify_vt_binop arg1 arg2 loc in
    Stack.push result value_stack;
    locals_secrecy, value_stack
  | WA.Call var ->
    let func_index = Int32.to_int var.WS.it in
    begin match List.nth wasm_func_secrecy func_index with
      |  (args_proto,result_proto,proto_name) ->
        let args = List.fold_left (fun acc _ ->
            (Stack.pop value_stack)::acc) [] args_proto
        in
        let ctr = ref 0 in
        List.iter2 (fun arg arg_proto ->
            if arg_proto = Public then
              assert_public arg
                (KPrint.bsprintf
                   "argument number %d of call to %s"
                   !ctr proto_name)
                loc;
            ctr := !ctr + 1
          ) args args_proto;
        Stack.push result_proto value_stack;
        locals_secrecy, value_stack
    end
  | WA.Drop ->
    ignore (Stack.pop value_stack);
    locals_secrecy, value_stack
  | WA.Loop ([], instrs) ->
    let loc = (L.While)::loc in
    check_instrs
      wasm_func_secrecy
      locals_secrecy
      value_stack
      func_result
      instrs
      loc
  | WA.If (_,tinstrs,finstrs) ->
    let if_arg = Stack.pop value_stack in
    assert_public if_arg "Branch condition" loc;
    let tstack = Stack.copy value_stack in
    let fstack = Stack.copy value_stack in
    let locT = (L.Then)::loc in
    let locals_secrecy, tstack_after =
      check_instrs
        wasm_func_secrecy
        locals_secrecy
        tstack
        func_result
        tinstrs
        locT
    in
    let locF = (L.Else)::loc in
    let locals_secrecy, fstack_after =
      check_instrs
        wasm_func_secrecy
        locals_secrecy
        fstack
        func_result
        finstrs
        locF
    in
    if tstack_after <> fstack_after then
      Warnings.maybe_fatal_error
        (KPrint.bsprintf "%a" L.ploc loc,
         Warnings.ConstantTimeValidatorFailure (
           "an if statement",
           "the result of both branches of an if statement should have the same secrecy"
         ));
    locals_secrecy, tstack_after
  | WA.Unary unop ->
    let arg = Stack.pop value_stack in
    let result = if constant_time_unop unop then
        unify_unop_ct arg
      else
        unify_unop_vt arg loc
    in
    Stack.push result value_stack;
    locals_secrecy, value_stack
  | WA.Convert _ ->
    locals_secrecy, value_stack
  | _ -> assert false


let check_module
    (secrecy_data : secrecy_data)
    (module_ : WA.module_')
    (module_name : string)
    (loc : loc)
  : unit =
  let module_secrecy_data = IdentMap.find module_name secrecy_data in
  let whole_module_secrecy_data : proto_secrecy list =
    (List.rev (List.fold_left (fun acc import ->
         match import.WS.it.WA.idesc.WS.it with
         | WA.FuncImport var ->
           let import_module_name = WU.encode import.WS.it.WA.module_name in
           begin try
               let import_module_funcs_secrecy =
                 IdentMap.find import_module_name secrecy_data
               in
               let (args,res,func_name) = List.find (fun (_,_,func_name) ->
                   func_name = WU.encode import.WS.it.WA.item_name
                 ) import_module_funcs_secrecy
               in
               (args,res,func_name)::acc
             with
             | Not_found ->
               match
                 (List.nth module_.WA.types (Int32.to_int var.WS.it)).WS.it
               with
               | WT.FuncType(args,_) ->
                 (List.map (fun _ -> Public) args,
                  Secret,
                  (WU.encode import.WS.it.WA.item_name))::acc
           end
         | _ -> acc
       ) [] module_.WA.imports))@module_secrecy_data
  in
  List.iter2 (fun func (proto_args,proto_result,proto_name) ->
      let locals_secrecy = LocalMap.empty in
      let (_,locals_secrecy) = List.fold_left
          (fun (index,locals_secrecy) arg_secret ->
             (Int32.add index Int32.one,
              LocalMap.add index arg_secret locals_secrecy)
          ) (Int32.zero,locals_secrecy) proto_args
      in
      let loc = (L.In (Printf.sprintf "function %s" proto_name))::loc in
      let _, value_stack = check_instrs
          whole_module_secrecy_data
          locals_secrecy
          (Stack.create ())
          proto_result
          func.WS.it.WA.body
          loc
      in
      assert (Stack.length value_stack = 1);
      let res = Stack.pop value_stack in
      if proto_result = Public then
        assert_public res "return value of a function" loc;
    ) module_.WA.funcs module_secrecy_data

let check_modules
    (secrecy_data : secrecy_data )
    (modules : (string * WA.module_) list)
  : unit =
  List.iter (fun (module_name, module_) ->
      let loc =  [L.File(module_name)] in
      if module_name <> "WasmSupport" then
        check_module secrecy_data module_.WS.it module_name loc
    ) modules
