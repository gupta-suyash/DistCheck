open Printf

(* Fetching command line arguments *)
let litmus	= ref "abc"
let store		= ref "efg"

let main =
begin
let speclist = [("-l", Arg.Set_string litmus, "Litmus testcase");
("-s", Arg.Set_string store, "Sets store semantics");
]
in let usage_msg = "DistCheck Options:"
in Arg.parse speclist 
						(fun anon -> print_endline ("Invalid argument: " ^ anon)) usage_msg;
print_endline ("Litmus Testcase: " ^ !litmus);
print_endline ("Store semantics: " ^ !store);
end

let () = main

