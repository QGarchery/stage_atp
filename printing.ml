open Format
let oc = open_out "/users/vals/garchery/Documents/stage_atp/printing.test"

let fmt = formatter_of_out_channel oc

let _ = fprintf fmt "hello\nmy name is Quentin";
        fprintf fmt "bla@.";
        close_out oc
          
  
