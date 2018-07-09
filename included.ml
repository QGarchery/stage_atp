let printint n = print_int n
let main : unit =
  for i = 1 to 10 do
    printint (i * i);
    print_newline ()
  done 
