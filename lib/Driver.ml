module I = Parser.MenhirInterpreter

let parse rule lexbuf =
  let rec loop (checkpoint : 'a I.checkpoint) =
    match checkpoint with
      | I.Accepted v -> Ok v
      | I.Rejected -> assert false
      | I.HandlingError _ -> Error "Syntax error"
      | I.Shifting _
      | I.AboutToReduce _ ->
        let checkpoint = I.resume checkpoint in
        loop checkpoint
      | I.InputNeeded _ ->
        let tok = Lexer.read lexbuf in
        let checkpoint = I.offer checkpoint (tok, Lexing.dummy_pos, Lexing.dummy_pos) in
        loop checkpoint in
  loop (rule Lexing.dummy_pos)
