open Cparse
open Genlab

let loop_flag = ref 0
let str_flag = ref 0
let str_env = ref []

let compile out decl_list =
  (* write prefixe *)
  Printf.fprintf out "\t.file	\"%s\"\n" Cparse.(!cfile);
  (* main function *)
  let tab = Array.make 4 "" in begin
    let rec compile_aux tab decl_list rho = match decl_list with
      | [] -> ()
      | (CDECL(_,s))::t -> begin
          Printf.ksprintf (add 0) "\t.comm\t%s,4,4\n" s;
          compile_aux tab t ((s, s^"(%rip)")::rho)
      end
      | (CFUN(_,s,args,(_,c)))::t -> begin
          Printf.ksprintf (add 2) "\t.globl\t%s\n\t.type\t%s, @function\n%s:\n\tpushq\t%%rbp\n\tmovq\t%%rsp, %%rbp\n" s s s;
          (* todo args *)
          compile_code c rho;
          Printf.ksprintf (add 2) "\tleave\n\tret\n\t.size\t%s, .-%s\n" s s;
          compile_aux tab t rho
      end

    and compile_code c rho = match c with
      | CBLOCK(decl_list, lc_list) ->
        let rec declare decl_list rho stack = match decl_list with
          | [] -> List.iter (fun (_,c) -> compile_code c rho) lc_list
          | (CDECL(_,s))::t -> begin
              Printf.ksprintf (add 2) "\tpushq\t$0\n";
              declare t ((s, Printf.sprintf "%d(%%rbp)" stack)::rho) (stack-8)
          end
          | _ -> failwith "CFUN in CBLOCK not supposed to happen"
        in declare decl_list rho (-8)

      | CEXPR(e) -> compile_expr e rho

      | CIF(cond, (_,c1), (_,c2)) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          compile_expr cond rho;
          Printf.ksprintf (add 2) "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" i;
          compile_code c1 rho;
          Printf.ksprintf (add 2) "\tjmp\t.L%d\n.L%d:\n" (i+1) i;
          compile_code c2 rho;
          Printf.ksprintf (add 2) ".L%d:\n" (i+1)
        end

      | CWHILE(cond, (_,exec)) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          Printf.ksprintf (add 2) ".L%d:\n" i;
          compile_expr cond rho;
          Printf.ksprintf (add 2) "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" (i+1);
          compile_code exec rho;
          Printf.ksprintf (add 2) "\tjmp\t.L%d\n.L%d:\n" i (i+1)
        end

      | CRETURN(r) -> begin
          match r with
          | None -> ()
          | Some(e) -> compile_expr e rho;
            Printf.ksprintf (add 2) "\tleave\n\tret\n"
        end


    and compile_expr e rho = match (e_of_expr e) with
      | VAR(s) -> begin match (assoc_opt s rho) with
          | Some(a) -> Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n" a
          | None -> failwith "Trying to call unreferenced variable: %s" s
        end

      | CST(x) -> Printf.ksprintf (add 2) "\tmovq\t$%d, %%rax\n" x

      | STRING(s) -> let a_opt = assoc_opt s (!str_env) and i = (!str_flag) in begin
          if i = 0 then Printf.ksprintf (add 0) "\t.section\t.rodata\n";
          let string_address a_opt i s = match a_opt with
            | Some(a) -> a
            | None -> let a = Printf.sprintf ".LC%d" i in begin
                str_flag := i+1;
                Printf.ksprintf (add 0) "%s:\n\t.string\t\"%s\"\n" a s;
                str_env := ((s, a))::(!str_env);
                a
              end
          in Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n" (string_address a_opt i s)
        end

      | SET_VAR(s,e1) -> begin match (assoc_opt s rho) with
          | Some(a) -> begin
              compile_expr e1 rho;
              Printf.ksprintf (add 2) "\tmovq\t%%rax, %s\n" a
            end
          | None -> failwith "Trying to set an unreferenced variable: %s" s
        end

      | SET_ARRAY(_) -> fail "SET_ARRAY"
      | CALL(_) -> fail "CALL"
      | OP1(op, e1) -> begin
          compile_expr e1 rho;
          match op with
          | M_POST_INC -> begin
              match (e_of_expr e1) with
              | VAR(s) -> let a = List.assoc s rho in Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n\tincq\t%s\n" a a
              | OP2(S_INDEX, t, i) -> fail "INC_TAB"
              | _ -> ()
            end
          | M_POST_DEC -> begin
              match (e_of_expr e1) with
              | VAR(s) -> let a = List.assoc s rho in Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n\tdecq\t%s\n" a a
              | OP2(S_INDEX, t, i) -> fail "DEC_TAB"
              | _ -> ()
            end
          | _ -> let string_of_op op = match op with
              | M_MINUS -> "negq"
              | M_NOT -> "notq"
              | M_PRE_INC -> "incq"
              | M_PRE_DEC -> "decq"
              | _ -> failwith "Matched above (just to avoid stupid warnings)"
            in Printf.ksprintf (add 2) "\t%s\t%%rax\n" (string_of_op op)
        end
      | OP2(op, e1, e2) -> begin
          compile_expr e2 rho;
          Printf.ksprintf (add 2) "\tpushq\t%%rax\n";
          compile_expr e1 rho;
          Printf.ksprintf (add 2) "\tpopq\t%%r10\n";
          match op with
          | S_MUL -> Printf.ksprintf (add 2) "\timulq\t%%r10\n"
          | S_DIV -> Printf.ksprintf (add 2) "\tcqto\n\tidivq\t%%r10\n"
          | S_MOD -> Printf.ksprintf (add 2) "\tcqto\n\tidivq\t%%r10\n\tmovq\t%%rdx, %%rax\n"
          | S_ADD -> Printf.ksprintf (add 2) "\taddq\t%%r10, %%rax\n"
          | S_SUB -> Printf.ksprintf (add 2) "\tsubq\t%%r10, %%rax\n"
          | S_INDEX -> fail "S_INDEX"
        end

      | CMP(op, e1, e2) -> begin
          compile_expr e2 rho;
          Printf.ksprintf (add 2) "\tpushq\t%%rax\n";
          compile_expr e1 rho;
          Printf.ksprintf (add 2) "\tpopq\t%%r10\n";
          let string_of_op op = match op with
            | C_LT -> "l"
            | C_LE -> "le"
            | C_EQ -> "e"
          in Printf.ksprintf (add 2) "\tcmpq\t%%r10, %%rax\n\tset%s\t%%al\n\tmovzbq\t%%al, %%rax\n" (string_of_op op)
        end

      | EIF(cond, e1, e2) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          compile_expr cond rho;
          Printf.ksprintf (add 2) "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" i;
          compile_expr e1 rho;
          Printf.ksprintf (add 2) "\tjmp\t.L%d\n.L%d:\n" (i+1) i;
          compile_expr e2 rho;
          Printf.ksprintf (add 2) ".L%d:\n" (i+1)
        end

      | ESEQ(l) -> List.iter (fun ex -> compile_expr ex rho) l

    and assoc_opt a l =
      try Some(List.assoc a l) with Not_found -> None

    and add i s = tab.(i) <- tab.(i) ^ s

    and fail m =
      let (s,a,b,c,d) = Cparse.getloc () in
      Printf.printf "%s > %s (%d,%d,%d,%d)\n" s m a b c d

    in compile_aux tab decl_list [];

    Printf.ksprintf (add 0) "\t.text\n";
    (* write the main x86 code *)
    for i = 0 to 3 do Printf.fprintf out "%s" tab.(i) done
  end;
  (* write_suffixe *)
  Printf.fprintf out "\t.ident\t\"MCC: (Ubuntu 5.4.0-6ubuntu1~16.04.10) 5.4.0 20160609\"\n\t.section\t.note.GNU-stack,\"\",@progbits"
