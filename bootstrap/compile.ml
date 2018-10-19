open Cparse
open Genlab

let compile out decl_list =
  (* write prefixe *)
  Printf.fprintf out "\t.file	\"ex1.c\"\n";
  (* main function *)
  let tab = Array.make 4 "" in begin
    let rec compile_aux tab decl_list = match decl_list with
      | [] -> ()
      | h::t -> begin match h with
          | CDECL(_,s) -> write ("\t.comm\t" ^ s ^ ",4,4\n") 0
          | CFUN(_,s,args,(_,c)) -> (* todo args *) compile_code c
        end;
        compile_aux tab t

    and compile_code c = match c with
      | CBLOCK(decl_list, lc_list) -> fail "CBLOCK"
      | CEXPR(le) -> fail "CEXPR"
      | CIF(cond, then_code, else_code) -> fail "CIF"
      | CWHILE(cond, exec) -> fail "CWHILE"
      | CRETURN(_) -> fail "CRETURN"

    and write s i = tab.(i) <- tab.(i) ^ s

    and fail m =
      let (s,a,b,c,d) = Cparse.getloc () in
      Printf.fprintf stdout "%s > %s (%d,%d,%d,%d)\n" s m a b c d

    in compile_aux tab decl_list;
    (* write the main x86 code *)
    for i = 0 to 3 do Printf.fprintf out "%s" tab.(i) done
  end;
  (* write_suffixe *)
  Printf.fprintf out "\t.ident\t\"MCC: (Ubuntu 5.4.0-6ubuntu1~16.04.10) 5.4.0 20160609\"\n\t.section\t.note.GNU-stack,\"\",@progbits"
