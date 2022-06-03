open Printer
open VCGen
open Easycrypt

let () =
  Arg.parse Commandline.options Commandline.argument Commandline.usage ;
  let precondition, prog, poscondition, time =
    try
      !Commandline.input |> open_in
      |> Lexing.from_channel ~with_positions:false
      |> Parser.parse Lexer.token
    with _ -> failwith "Parsing Error"
  in
  let result = vcg precondition prog time poscondition in
  let oc = open_out_gen [Open_append; Open_creat] 0o644 "output.ec" in
  let easycrypt = vcs_to_easycrypt result in
  Printf.printf "\n\n***%d VC's Generated ***\n\n" (List.length result) ;
  Printf.fprintf oc "%s\n" easycrypt ;
  close_out oc ;
  print result
