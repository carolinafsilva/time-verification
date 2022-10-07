let program_name = "main"

let usage = Format.sprintf "usage: ./%s.exe [options] file\n\nVC\n" program_name

let input = ref ""

let proof_mode = ref false

let options =
  [
    ("--easycrypt", Arg.String (fun _ -> ()), "");
    ("-p", Arg.Set proof_mode, "generate VCs for program");
    ("--proof", Arg.Set proof_mode, "generate VCs for program");
    ("-h", Arg.Unit (fun _ -> ()), "print this help menu");
    ("-help", Arg.Unit (fun _ -> ()), "print this help menu");
    ("--help", Arg.Unit (fun _ -> ()), "print this help menu");
  ]

let argument s = input := s
