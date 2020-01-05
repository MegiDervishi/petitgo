open Format
open X86_64
open Go_ast
(** TO DO : MAKEFILE -> DELETE .s files *)

let frame_size = ref 0
let (genv : (string, unit) Hashtbl.t) = Hashtbl.create 17
module StrMap = Map.Make(String)

let compile_program p ofile =
  if !frame_size mod 16 = 0 then frame_size := !frame_size + 8;
  let p =
    { text = 
        globl "main" ++ label "main" ++ pushq !%rbp ++ (* for  all func *)
        subq (imm !frame_size) !%rsp ++ (* alloue la frame *)
        leaq (ind ~ofs:(!frame_size - 8) rsp) rbp ++ (* %rbp = ... *)
        addq (imm !frame_size) !%rsp ++ (* désalloue la frame *) popq rbp ++
        movq (imm 0) !%rax ++ (* exit *)
        ret ++
        label "print_int" ++
        movq !%rdi !%rsi ++
        leaq (lab ".Sprint_int") rdi ++
        movq (imm 0) !%rax ++
        call "printf" ++
        ret;
      data =
        Hashtbl.fold (fun x _ l -> label x ++ dquad [1] ++ l) genv
          (label ".Sprint_int" ++ string "%d\n")
    }
  in
  let f = open_out ofile in
  let fmt = formatter_of_out_channel f in
  X86_64.print_program fmt p;
  fprintf fmt "@?";
  close_out f