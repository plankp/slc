open Slc

(*
let program =
  Module (["fst"], ref (
    LetFun ((1, [2], 10, 20, ref (
      LetFun ((3, [4], 11, 21, ref (
        Jmp (11, [2]))), ref (
      Jmp (10, [3]))))), ref (
    Export ["fst", 1]))))

let program =
  Module (["snd"], ref (
    LetFun ((1, [2], 10, 20, ref (
      LetFun ((3, [4], 11, 21, ref (
        Jmp (11, [4]))), ref (
      Jmp (10, [3]))))), ref (
    Export ["snd", 1]))))

let program =
  Module (["snd"], ref (
    LetRec (
      [ (1, [2], 10, 20, ref (Jmp (10, [3])))
      ; (3, [4], 11, 21, ref (Jmp (11, [4])))
      ], ref (Export ["snd", 1]))))

let program =
  Module (["inf1"], ref (
    LetRec (
      [ (1, [], 10, 20, ref (App (3, [], 10, 20)))
      ; (3, [], 11, 21, ref (App (1, [], 11, 21)))
      ], ref (Export ["inf1", 1]))))

let program =
  Module (["inf2"], ref (
    LetFun ((1, [4; 5], 2, 10, ref (
      LetCont ([3, [6; 7], ref (Jmp (3, [7; 6]))], ref (
      Jmp (3, [5; 4]))))), ref (
    Export ["inf2", 1]))))

let program =
  Module (["inf3"], ref (
    LetFun ((1, [4; 5], 2, 10, ref (
      LetRec (
        [ (3, [6; 7], 9, 20, ref (App (3, [7; 6], 9, 20)))
        ], ref (App (3, [5; 4], 2, 10))))), ref (
      Export ["inf3", 1]))))

let program =
  Module (["bad"], ref (
    LetRec (
      [ (1, [2; 3], 10, 20, ref (
          LetCont ([11, [4], ref (Jmp (10, [4]))], ref (
          App (1, [2; 3], 11, 20)))))
      ], ref (Export ["bad", 1]))))

let program =
  Module (["id"], ref (
    LetFun ((1, [2], 3, 10, ref (
      LetRec ([4, [5], 6, 20, ref (Jmp (6, [5]))], ref (
      LetCont ([7, [8], ref (Jmp (3, [8]))], ref (
      App (4, [2], 7, 10))))))), ref (
    Export ["id", 1]))))
*)

let program =
  Ast.Module (["ulist"; "nil"], ref (
    Ast.LetCons (1, 0, [], ref (
      Ast.LetPack (2, [], ref (
        Ast.LetCons (1, 1, [2; 1], ref (
          Ast.LetCont ([3, [4; 5], ref (Ast.Export ["ulist", 1; "nil", 5])], ref (
            Ast.Case (1, Ast.M.singleton (Some 1) 3)))))))))))

let () =
  print_endline "Original";
  Ast.dump program;
  print_endline "";
  print_endline "";

  print_endline "Fixrec";
  PassFixrec.transform program;
  Ast.dump program;
  print_endline "";
  print_endline "";

  print_endline "Contification";
  PassContify.transform program;
  Ast.dump program;
  print_endline "";
  print_endline "";

  print_endline "Closure Conversion";
  PassCC.transform program;
  Ast.dump program;
  print_endline "";
  print_endline "";

  print_endline "Lower to C";
  PassLower.lower program
