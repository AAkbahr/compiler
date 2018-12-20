open Cparse
open Genlab

let loop_flag = ref 0
let str_flag = ref 0
let str_env = ref []
let fun_env = ref ["fopen";"malloc";"calloc";"realloc";"exit"]
let exn_flag = ref 2
let exn_env = ref []
let try_flag = ref 1
let rho_saved = ref []

let assoc_opt a l =
  try Some(List.assoc a l) with Not_found -> None

(* TOOLS FOR x86 WRITING *)

let tab = Array.make 4 ""

let add t i s = t.(i) <- t.(i)^s

let write i = Printf.ksprintf (add tab i)

(* COMPILER *)

let compile out decl_list =
  (* write prefixe *)
  Printf.fprintf out "\t.file	\"%s\"\n" Cparse.(!cfile);
  (* main function *)
  begin
    let rec compile_aux decl_list = match decl_list with
      | [] -> ()
      | (CDECL(_,s))::t -> begin
          write 0 "\t.comm\t%s,8,8\n" s;
          compile_aux t
      end
      | (CFUN(_,s,args,(_,c)))::t -> begin
          write 2 "\t.globl\t%s\n\t.type\t%s, @function\n%s:\n\tpushq\t%%rbp\n\tmovq\t%%rsp, %%rbp\n" s s s;
          fun_env := s::(!fun_env);

          let rec add_args args regs i rho stack = match args with
            | [] -> rho

            | (CDECL(_,s))::t -> if i < 7 then begin
                (* the 6 first args are moved into specific registers *)
                write 2 "\tpushq\t%s\n" regs.(i-1);
                add_args t regs (i+1) ((s, Printf.sprintf "%d(%%rbp)" (-8*i))::rho) stack
              end
              else begin
                (* the last args are pushed on the stack *)
                write 2 "\tpushq\t%d(%%rbp)\n" (8*stack);
                add_args t regs (i+1) ((s, Printf.sprintf "%d(%%rbp)" (-8*i))::rho) (stack+1)
              end

            | _ -> failwith "Only variable declaration can be arg of a function"

          in let rho = add_args args [|"%rdi";"%rsi";"%rdx";"%rcx";"%r8";"%r9"|] 1 [] 2 in begin
            (* once args are added, we compile the code of the function... *)
            compile_code c rho 0;
            (* ...we write the suffix of the function...*)
            write 2 "\tleave\n\tret\n\t.size\t%s, .-%s\n" s s;
            (* ...and we finally compile the rest of the code *)
            compile_aux t
          end
      end

    and compile_code c rho t_id = match c with
      | CBLOCK(decl_list, lc_list) ->
        let rec declare decl_list rho stack = match decl_list with
          | [] -> begin
              (* the environment is printed in the assembly code (debug) *)
              print_rho rho;
              (* instructions are successively compiled *)
              List.iter (fun (_,c) -> compile_code c rho t_id) lc_list;
              rho_saved := rho
          end
          | (CDECL(_,s))::t -> begin
              (* each variable is initialized to 0 and pushed on the stack *)
              write 2 "\tpushq\t$0\n";
              declare t ((s, Printf.sprintf "%d(%%rbp)" (-8*stack))::rho) (stack+1)
            end
          | _ -> failwith "CFUN in CBLOCK not supposed to happen"
        in declare decl_list rho (List.length rho +1)

      | CEXPR(e) -> compile_expr e rho t_id

      | CIF(cond, (_,c1), (_,c2)) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          compile_expr cond rho t_id;
          (* if the condition is not satisfied, we skip instructions of c1 *)
          write 2 "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" i;
          compile_code c1 rho t_id;
          (* if instructions of c1 are read, we skip instructions of c2 *)
          write 2 "\tjmp\t.L%d\n.L%d:\n" (i+1) i;
          compile_code c2 rho t_id;
          write 2 ".L%d:\n" (i+1)
        end

      | CWHILE(cond, (_,exec)) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          write 2 ".L%d:\n" i;
          compile_expr cond rho t_id;
          (* if cond is not satisfied, we jump after the instructions of exec *)
          write 2 "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" (i+1);
          rho_saved := rho;
          compile_code exec rho t_id;
          (* we ensure that all variables pushed during the loop are popped before ending, to avoid segfaults in big loops *)
          clean_env rho;
          (* when exec has been read, we jump back to the evaluation of cond *)
          write 2 "\tjmp\t.L%d\n.L%d:\n" i (i+1)
        end

      | CRETURN(r) -> begin
          match r with
          | None -> ()
          | Some(e) -> compile_expr e rho t_id;
            (* if the instruction is not in a try block, just leave ant ret *)
            if t_id = 0 then write 2 "\tleave\n\tret\n"
            (* otherwise save the returned value and jump to the finally *)
            else begin
              (* a return instruction in a try block is treated as a kind of exception *)
              write 2 "\tmovq\t$1, %%r14\n";
              write 2 "\tmovq\t%%rax, %%r15\n"
            end
        end

      | CTHROW(s, e) -> begin
          compile_expr e rho t_id;
          write 2 "\tmovq\t%%rax, %%r15\n";
          write 2 "\tmovq\t$%d, %%r14\n" (exn_id s);
          if t_id = 0 then write 2 "\tmovq\t$1, %%rax\n\tleave\n\tret\n"
          else begin
            clean_env rho;
            write 2 "\tjmp\t.XC%d\n" t_id
          end
        end

      | CTRY((_,c), hl, fc) -> let i = !try_flag in begin
          try_flag := !try_flag + 1;
          rho_saved := rho;
          compile_code c rho i;
          (* if no exception is detected, jump directly to the finally *)
          write 2 "\tcmpq\t$1, %%r14\n\tjle\t.XF%d\n" i;
          write 2 ".XC%d:\n" i;
          let rec catch_exn hl = match hl with
            | [] -> ()
            | (ex,x,(_,c))::t -> let j = exn_id ex in begin
                (* check if the handler corresponds to a thrown exception *)
                write 2 "\tcmpq\t$%d, %%r14\n" j;
                write 2 "\tjne\t.XC%de%d\n" i j;
                (* resolve the exception *)
                write 2 "\tmovq\t$0, %%r14\n";
                (* get the value of the exception *)
                write 2 "\tpushq\t%%r15\n";
                compile_code c ((x, Printf.sprintf "-%d(%%rbp)" (8*(List.length rho + 1)))::rho) t_id;
                write 2 "\tpopq\t%%rax\n";
                (* go directly to the finally statement *)
                write 2 "\tjmp\t.XF%d\n" i;
                write 2 ".XC%de%d:\n" i j;
                catch_exn t
              end
          in catch_exn hl;
          write 2 ".XF%d:\n" i;
          let finally_exn fc = match fc with
            | Some((_,c)) -> compile_code c rho t_id
            | None -> ()
          in finally_exn fc;
          (* if there is no exception, no more things to do *)
          write 2 "\tcmpq\t$0, %%r14\n";
          write 2 "\tje\t.XE%d\n" i;
          write 2 "\tmovq\t$1, %%rax\n";
          (* if there is a return statement from the try block... *)
          write 2 "\tcmpq\t$1, %%r14\n";
          write 2 "\tjne\t.XL%d\n" i;
          (* ...consider it as a solved exception... *)
          write 2 "\tmovq\t$0, %%r14\n";
          (* ...and move the returned value into %rax *)
          write 2 "\tmovq\t%%r15, %%rax\n";
          write 2 ".XL%d:\n" i;
          if t_id = 0 then write 2 "\tleave\n\tret\n"
          else write 2 "\tjmp\t.XC%d\n" t_id;
          write 2 ".XE%d:\n" i
        end

    and compile_expr e rho t_id = match (e_of_expr e) with
      | VAR(s) -> write 2 "\tmovq\t%s, %%rax\n" (assoc_loc s rho)

      | CST(x) -> write 2 "\tmovq\t$%d, %%rax\n" x

      | STRING(s) -> let a_opt = assoc_opt s (!str_env) and i = (!str_flag) in begin
          if i = 0 then write 1 "\t.section\t.rodata\n";
          let string_address a_opt i s = match a_opt with
            (* if the string is already in str_env, its address is known *)
            | Some(a) -> a
            (* otherwise we add it and write the necesary x86 code at the beginning of the file *)
            | None -> let a = Printf.sprintf ".LC%d" i in begin
                str_flag := i+1;
                write 1 "%s:\n\t.string\t\"%s\"\n" a (String.escaped s);
                str_env := ((s, a))::(!str_env);
                a
              end
          in write 2 "\tmovq\t$%s, %%rax\n" (string_address a_opt i s)
        end

      | SET_VAR(s,e1) -> begin
          compile_expr e1 rho t_id;
          write 2 "\tmovq\t%%rax, %s\n" (assoc_loc s rho)
        end

      | SET_ARRAY(t,i,e) -> begin
          (* we compile and push the expression e... *)
          compile_expr e rho t_id;
          write 2 "\tpushq\t%%rax\n";
          (* ...then we compile i... *)
          compile_expr i rho t_id;
          (* ...we pop e in r%13... *)
          write 2 "\tpopq\t%%r13\n";
          (* ...and move i in r%10. *)
          write 2 "\tmovq\t%%rax, %%r10\n";
          (* now we move the address of t in %rax... *)
          write 2 "\tmovq\t%s, %%rax\n" (assoc_loc t rho);
          (* add 8*i to this address to get the address of t[i]... *)
          write 2 "\timulq\t$8, %%r10\n";
          write 2 "\taddq\t%%r10, %%rax\n";
          (* ...and finally we move e to the address %rax points to *)
          write 2 "\tmovq\t%%r13, (%%rax)\n";
          write 2 "\tmovq\t%%r13, %%rax\n"
        end

      | CALL(f,args) -> let rec add_args f args regs i = match args with
          | [] -> begin
              write 2 "\tmovq\t$0, %%rax\n\tcall\t%s\n" f;
              if not (List.mem f (!fun_env)) then write 2 "\tmovslq\t%%eax, %%rax\n";
              (* exception handling *)
              write 2 "\tcmpq\t$1, %%r14\n";
              (* if no exception handled, the following instructions are skipped *)
              write 2 "\tjle\t.L%d\n" !loop_flag;
              if t_id = 0 then write 2 "\tleave\n\tret\n"
              else begin
                clean_env rho;
                write 2 "\tjmp\t.XC%d\n" t_id
              end;
              write 2 ".L%d:\n" !loop_flag;
              loop_flag := !loop_flag + 1
            end
          | h::t -> begin
              compile_expr h rho t_id;
              if i > 6 then write 2 "\tpushq\t%%rax\n"
              else write 2 "\tmovq\t%%rax, %s\n" regs.(i-1);
              add_args f t regs (i-1)
            end
        in add_args f (List.rev args) [|"%rdi";"%rsi";"%rdx";"%rcx";"%r8";"%r9"|] (List.length args)

      | OP1(op, e1) -> begin
          compile_expr e1 rho t_id;
          match op with
          | M_MINUS -> write 2 "\tnegq\t%%rax\n"
          | M_NOT -> write 2 "\tnotq\t%%rax\n"
          | _ -> match (e_of_expr e1) with
            | VAR(s) -> let a = assoc_loc s rho in begin match op with
                | M_POST_INC -> write 2 "\tincq\t%s\n" a
                | M_POST_DEC -> write 2 "\tdecq\t%s\n" a
                | M_PRE_INC -> write 2 "\tincq\t%%rax\n\tincq\t%s\n" a
                | M_PRE_DEC -> write 2 "\tdecq\t%%rax\n\tdecq\t%s\n" a
                | _ -> failwith "Matched above"
              end
            | OP2(S_INDEX, t, i) -> begin
                compile_expr i rho t_id;
                write 2 "\tpushq\t%%rax\n";
                compile_expr t rho t_id;
                write 2 "\tpopq\t%%r10\n";
                write 2 "\timulq\t$8, %%r10\n";
                write 2 "\taddq\t%%rax, %%r10\n";
                let inc = "\tincq\t(%r10)\n" and dec = "\tdecq\t(%r10)\n" and mov = "\tmovq\t(%r10), %rax\n" in
                match op with
                | M_POST_INC -> write 2 "%s%s" mov inc
                | M_POST_DEC -> write 2 "%s%s" mov dec
                | M_PRE_INC -> write 2 "%s%s" inc mov
                | M_PRE_DEC -> write 2 "%s%s" dec mov
                | _ -> failwith "Just to satisfy the compiler"
            end
            | _ -> match op with
              | M_PRE_INC -> write 2 "\tincq\t%%rax\n"
              | M_PRE_DEC -> write 2 "\tdecq\t%%rax\n"
              | _ -> ()
        end

      | OP2(op, e1, e2) -> begin
          (* e2 is evaluated first and saved in %r10 *)
          compile_expr e2 rho t_id;
          write 2 "\tpushq\t%%rax\n";
          compile_expr e1 rho t_id;
          write 2 "\tpopq\t%%r10\n";
          (* at this step e1 is in %rax and e2 in %r10 *)
          match op with
          | S_MUL -> write 2 "\timulq\t%%r10\n"
          | S_DIV -> write 2 "\tcqto\n\tidivq\t%%r10\n"
          | S_MOD -> write 2 "\tcqto\n\tidivq\t%%r10\n\tmovq\t%%rdx, %%rax\n"
          | S_ADD -> write 2 "\taddq\t%%r10, %%rax\n"
          | S_SUB -> write 2 "\tsubq\t%%r10, %%rax\n"
          | S_INDEX -> write 2 "\tmovq\t(%%rax,%%r10,8), %%rax\n"
        end

      | CMP(op, e1, e2) -> begin
          compile_expr e2 rho t_id;
          write 2 "\tpushq\t%%rax\n";
          compile_expr e1 rho t_id;
          write 2 "\tpopq\t%%r10\n";
          let string_of_op op = match op with
            | C_LT -> "l"
            | C_LE -> "le"
            | C_EQ -> "e"
          in write 2 "\tcmpq\t%%r10, %%rax\n\tset%s\t%%al\n\tmovzbq\t%%al, %%rax\n" (string_of_op op)
        end

      | EIF(cond, e1, e2) -> let i = !loop_flag in begin
          loop_flag := i + 2;
          compile_expr cond rho t_id;
          write 2 "\tcmpq\t$0, %%rax\n\tje\t.L%d\n" i;
          compile_expr e1 rho t_id;
          write 2 "\tjmp\t.L%d\n.L%d:\n" (i+1) i;
          compile_expr e2 rho t_id;
          write 2 ".L%d:\n" (i+1)
        end

      | ESEQ(l) -> List.iter (fun ex -> compile_expr ex rho t_id) l

    and assoc_loc a l =
      try List.assoc a l with Not_found -> Printf.sprintf "%s(%%rip)" a

    and clean_env rho =
      for i = 1 to abs (List.length !rho_saved - List.length rho) do
        write 2 "\tpopq\t%%rbx\n"
      done

    and exn_id s = match assoc_opt s (!exn_env) with
      | Some(i) -> i
      | None -> let i = !exn_flag in begin
          exn_flag := i+1;
          exn_env := (s,i)::(!exn_env);
          i
        end

    (* print the environment as a comment in the x86 code (debug) *)
    and print_rho rho =
      let rec aux rho acc = match rho with
        | [] -> write 2 "%s] */\n" acc
        | (s,a)::t -> aux t (Printf.sprintf "%s%s:%s; " acc s a)
      in aux rho "/* ["

    in compile_aux decl_list;

    write 1 "\t.text\n";
    (* write the main x86 code *)
    for i = 0 to 3 do Printf.fprintf out "%s" tab.(i) done
  end;
  (* write_suffixe *)
  Printf.fprintf out "\t.ident\t\"MCC: (Ubuntu 5.4.0-6ubuntu1~16.04.10) 5.4.0 20160609\"\n\t.section\t.note.GNU-stack,\"\",@progbits"
