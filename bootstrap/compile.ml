open Cparse
open Genlab

let loop_flag = ref 0
let str_flag = ref 0
let str_env = ref []
let fun_env = ref ["fopen";"malloc";"calloc";"realloc";"exit"]

let compile out decl_list =
  (* write prefixe *)
  Printf.fprintf out "\t.file	\"%s\"\n" Cparse.(!cfile);
  (* main function *)
  let tab = Array.make 4 "" in begin
    let rec compile_aux tab decl_list = match decl_list with
      | [] -> ()
      | (CDECL(_,s))::t -> begin
          Printf.ksprintf (add 0) "\t.comm\t%s,4,4\n" s;
          compile_aux tab t
      end
      | (CFUN(_,s,args,(_,c)))::t -> begin
          Printf.ksprintf (add 2) "\t.globl\t%s\n\t.type\t%s, @function\n%s:\n\tpushq\t%%rbp\n\tmovq\t%%rsp, %%rbp\n" s s s;
          fun_env := s::(!fun_env);

          let rec add_args args regs i rho stack = match args with
            | [] -> rho

            | (CDECL(_,s))::t -> if i < 7 then begin
                Printf.ksprintf (add 2) "\tpushq\t%s\n" regs.(i-1);
                add_args t regs (i+1) ((s, Printf.sprintf "%d(%%rbp)" (-8*i))::rho) stack
              end
              else begin
                Printf.ksprintf (add 2) "\tpushq\t%d(%%rbp)\n" (8*stack);
                add_args t regs (i+1) ((s, Printf.sprintf "%d(%%rbp)" (-8*i))::rho) (stack+1)
              end

            | _ -> failwith "Only variable declaration can be arg of a function"

          in let rho = add_args args [|"%rdi";"%rsi";"%rdx";"%rcx";"%r8";"%r9"|] 1 [] 2 in begin
            compile_code c rho;
            Printf.ksprintf (add 2) "\tleave\n\tret\n\t.size\t%s, .-%s\n" s s;
            compile_aux tab t
          end
      end

    and compile_code c rho = match c with
      | CBLOCK(decl_list, lc_list) ->
        let rec declare decl_list rho stack = match decl_list with
          | [] -> print_rho rho; List.iter (fun (_,c) -> compile_code c rho) lc_list
          | (CDECL(_,s))::t -> begin
              Printf.ksprintf (add 2) "\tpushq\t$0\n";
              declare t ((s, Printf.sprintf "%d(%%rbp)" (-8*stack))::rho) (stack+1)
            end
          | _ -> failwith "CFUN in CBLOCK not supposed to happen"
        in declare decl_list rho (List.length rho +1)

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
      | VAR(s) -> Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n" (assoc_loc s rho)

      | CST(x) -> Printf.ksprintf (add 2) "\tmovq\t$%d, %%rax\n" x

      | STRING(s) -> let a_opt = assoc_opt s (!str_env) and i = (!str_flag) in begin
          if i = 0 then Printf.ksprintf (add 0) "\t.section\t.rodata\n";
          let string_address a_opt i s = match a_opt with
            | Some(a) -> a
            | None -> let a = Printf.sprintf ".LC%d" i in begin
                str_flag := i+1;
                Printf.ksprintf (add 0) "%s:\n\t.string\t\"%s\"\n" a (String.escaped s);
                str_env := ((s, a))::(!str_env);
                a
              end
          in Printf.ksprintf (add 2) "\tmovq\t$%s, %%rax\n" (string_address a_opt i s)
        end

      | SET_VAR(s,e1) -> begin
          compile_expr e1 rho;
          Printf.ksprintf (add 2) "\tmovq\t%%rax, %s\n" (assoc_loc s rho)
        end

      | SET_ARRAY(t,i,e) -> begin
          compile_expr e rho;
          Printf.ksprintf (add 2) "\tpushq\t%%rax\n";
          compile_expr i rho;
          Printf.ksprintf (add 2) "\tpopq\t%%r13\n"; (* %r10 <- e *)
          Printf.ksprintf (add 2) "\tmovq\t%%rax, %%r10\n"; (* %r13 <- i *)
          Printf.ksprintf (add 2) "\tmovq\t%s, %%rax\n" (assoc_loc t rho); (* %rax <- t *)
          Printf.ksprintf (add 2) "\timulq\t$8, %%r10\n";
          Printf.ksprintf (add 2) "\taddq\t%%r10, %%rax\n";
          Printf.ksprintf (add 2) "\tmovq\t%%r13, (%%rax)\n";
          Printf.ksprintf (add 2) "\tmovq\t%%r13, %%rax\n"
        end

      | CALL(f,args) -> let rec add_args f args regs i = match args with
          | [] -> begin
              Printf.ksprintf (add 2) "\tmovq\t$0, %%rax\n\tcall\t%s\n" f;
              if not (List.mem f (!fun_env)) then Printf.ksprintf (add 2) "\tmovslq\t%%eax, %%rax\n"
            end
          | h::t -> begin
              compile_expr h rho;
              if i > 6 then Printf.ksprintf (add 2) "\tpushq\t%%rax\n"
              else Printf.ksprintf (add 2) "\tmovq\t%%rax, %s\n" regs.(i-1);
              add_args f t regs (i-1)
            end
        in add_args f (List.rev args) [|"%rdi";"%rsi";"%rdx";"%rcx";"%r8";"%r9"|] (List.length args)

      | OP1(op, e1) -> begin
          compile_expr e1 rho;
          match op with
          | M_MINUS -> Printf.ksprintf (add 2) "\tnegq\t%%rax\n"
          | M_NOT -> Printf.ksprintf (add 2) "\tnotq\t%%rax\n"
          | _ -> match (e_of_expr e1) with
            | VAR(s) -> let a = assoc_loc s rho in begin match op with
                | M_POST_INC -> Printf.ksprintf (add 2) "\tincq\t%s\n" a
                | M_POST_DEC -> Printf.ksprintf (add 2) "\tdecq\t%s\n" a
                | M_PRE_INC -> Printf.ksprintf (add 2) "\tincq\t%%rax\n\tincq\t%s\n" a
                | M_PRE_DEC -> Printf.ksprintf (add 2) "\tdecq\t%%rax\n\tdecq\t%s\n" a
                | _ -> failwith "Just to satisfy the compiler"
              end
            | OP2(S_INDEX, t, i) -> begin
                compile_expr i rho;
                Printf.ksprintf (add 2) "\tpushq\t%%rax\n";
                compile_expr t rho;
                Printf.ksprintf (add 2) "\tpopq\t%%r10\n";
                Printf.ksprintf (add 2) "\timulq\t$8, %%r10\n";
                Printf.ksprintf (add 2) "\taddq\t%%rax, %%r10\n";
                let inc = "\tincq\t(%r10)\n" and dec = "\tdecq\t(%r10)\n" and mov = "\tmovq\t(%r10), %rax\n" in
                match op with
                | M_POST_INC -> Printf.ksprintf (add 2) "%s%s" mov inc
                | M_POST_DEC -> Printf.ksprintf (add 2) "%s%s" mov dec
                | M_PRE_INC -> Printf.ksprintf (add 2) "%s%s" inc mov
                | M_PRE_DEC -> Printf.ksprintf (add 2) "%s%s" dec mov
                | _ -> failwith "Just to satisfy the compiler"
            end
            | _ -> match op with
              | M_PRE_INC -> Printf.ksprintf (add 2) "\tincq\t%%rax\n"
              | M_PRE_DEC -> Printf.ksprintf (add 2) "\tdecq\t%%rax\n"
              | _ -> ()
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
          | S_INDEX -> Printf.ksprintf (add 2) "\tmovq\t(%%rax,%%r10,8), %%rax\n"
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

    and assoc_loc a l =
      try List.assoc a l with Not_found -> Printf.sprintf "%s(%%rip)" a

    and add i s = tab.(i) <- tab.(i) ^ s

    and print_rho rho =
      let rec aux rho acc = match rho with
        | [] -> Printf.ksprintf (add 2) "%s] */\n" acc
        | (s,a)::t -> aux t (Printf.sprintf "%s%s:%s; " acc s a)
      in aux rho "/* ["

    (* and fail m =
      let (s,a,b,c,d) = Cparse.getloc () in
       Printf.printf "%s > %s (%d,%d,%d,%d)\n" s m a b c d *)
    in compile_aux tab decl_list;

    Printf.ksprintf (add 0) "\t.text\n";
    (* write the main x86 code *)
    for i = 0 to 3 do Printf.fprintf out "%s" tab.(i) done
  end;
  (* write_suffixe *)
  Printf.fprintf out "\t.ident\t\"MCC: (Ubuntu 5.4.0-6ubuntu1~16.04.10) 5.4.0 20160609\"\n\t.section\t.note.GNU-stack,\"\",@progbits"
