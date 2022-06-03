let program_name = "main"

let usage = Format.sprintf "usage: ./%s.exe [options] file\n\nVC\n" program_name

let input = ref ""

let options =
  [
    ("--easycrypt", Arg.String (fun _ -> ()), "");
    ("-h", Arg.Unit (fun _ -> ()), "print this help menu");
    ("-help", Arg.Unit (fun _ -> ()), "print this help menu");
    ("--help", Arg.Unit (fun _ -> ()), "print this help menu");
  ]

let argument s = input := s
