open Ast

(*
let program =
  Module (ref
    (LetFun (1, [2], 10, ref (
      LetFun (3, [4], 11, ref (
        Jmp (11, [2])), ref (
        Jmp (10, [3])))), ref (
      Export ["fst", 1]))))
*)

(*
let program =
  Module (ref
    (LetFun (1, [2], 10, ref (
      LetFun (3, [4], 11, ref (
        Jmp (11, [4])), ref (
        Jmp (10, [3])))), ref (
      Export ["snd", 1]))))
*)

(*
let program =
  Module (ref
    (LetRec (
      [ (1, [2], 10, ref (Jmp (10, [3])))
      ; (3, [4], 11, ref (Jmp (11, [4])))
      ], ref (Export ["snd", 1]))))
*)

(*
let program =
  Module (ref
    (LetRec (
      [ (1, [], 10, ref (App (3, [], 10)))
      ; (3, [], 11, ref (App (1, [], 11)))
      ], ref (Export ["inf1", 1]))))
*)

(*
let program =
  Module (ref
    (LetFun (1, [4; 5], 2, ref (
      LetCont (3, [6; 7], ref (Jmp (3, [7; 6])), ref (Jmp (3, [5; 4])))),
      ref (Export ["inf2", 1]))))
*)

(*
let program =
  Module (ref
    (LetFun (1, [4; 5], 2, ref (
      LetRec (
        [ (3, [6; 7], 9, ref (App (3, [7; 6], 9)))
        ], ref (App (3, [5; 4], 2)))),
      ref (Export ["inf3", 1]))))
*)

(*
let program =
  Module (ref
    (LetRec (
      [ (1, [2; 3], 10, ref (
          LetCont (11, [4], ref (Jmp (10, [4])), ref (
            App (1, [2; 3], 11)))))
      ], ref (Export ["bad", 1]))))
*)

let program =
  Module (ref (
    LetFun (1, [2], 3, ref (
      LetFun (4, [5], 6, ref (
        Jmp (6, [5])), ref (
        LetCont (7, [8], ref (
          Jmp (3, [8])), ref (
          App (4, [2], 7)))))), ref (
      Export ["id", 1]))))

let () =
  print_endline "Original";
  dump program;
  print_endline "";
  print_endline "";

  print_endline "Contification";
  PassContify.transform program;
  dump program;
  print_endline "";
  print_endline "";

  print_endline "Closure Conversion";
  PassCC.transform program;
  dump program;
  print_endline "";
  print_endline "";

  print_endline "Lower to C";
  PassLower.lower program
