(* ========================================================================= *)
(* Reading the p1 export tisa/manifests/tisa_x86_p1_programs_v2.json: each   *)
(* program's HOL text, image bytes and spans, for the image prover.          *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_image.ml";;

type tisa_json =
  | Tjstr of string
  | Tjnum of string
  | Tjarr of tisa_json list
  | Tjobj of (string * tisa_json) list
  | Tjbool of bool
  | Tjnull;;

let tisa_json_parse (s:string) =
  let n = String.length s and pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else ' ' in
  let ws () = while !pos < n && String.contains " \n\t\r" s.[!pos] do incr pos done in
  let expect c =
    ws(); if !pos < n && s.[!pos] = c then incr pos
          else failwith (Printf.sprintf "json: expected %c at %d" c !pos) in
  let str () =
    expect '"';
    let b = Buffer.create 64 in
    while !pos < n && s.[!pos] <> '"' do
      (if s.[!pos] = '\\' && !pos + 1 < n then
         (incr pos; Buffer.add_char b (match s.[!pos] with 'n' -> '\n' | 't' -> '\t' | c -> c))
       else Buffer.add_char b s.[!pos]);
      incr pos
    done;
    expect '"'; Buffer.contents b in
  let rec value () =
    ws();
    match peek() with
    | '"' -> Tjstr(str())
    | '{' -> incr pos; ws();
             if peek() = '}' then (incr pos; Tjobj []) else
             let rec fields acc =
               let k = (ws(); str()) in
               expect ':';
               let v = value() in
               ws();
               if peek() = ',' then (incr pos; fields ((k,v)::acc))
               else (expect '}'; Tjobj(rev((k,v)::acc))) in
             fields []
    | '[' -> incr pos; ws();
             if peek() = ']' then (incr pos; Tjarr []) else
             let rec items acc =
               let v = value() in
               ws();
               if peek() = ',' then (incr pos; items (v::acc))
               else (expect ']'; Tjarr(rev(v::acc))) in
             items []
    | 't' -> pos := !pos + 4; Tjbool true
    | 'f' -> pos := !pos + 5; Tjbool false
    | 'n' -> pos := !pos + 4; Tjnull
    | _ -> let st = !pos in
           while !pos < n && String.contains "0123456789+-.eE" s.[!pos] do incr pos done;
           if !pos = st then failwith (Printf.sprintf "json: unexpected character at %d" st);
           Tjnum(String.sub s st (!pos - st)) in
  let v = value() in
  ws(); if !pos <> n then failwith "json: trailing text"; v;;

let tisa_json_field ob k =
  match ob with Tjobj l -> (try assoc k l with Failure _ -> failwith ("json: no field " ^ k))
             | _ -> failwith "json: not an object";;
let tisa_json_str = function Tjstr s -> s | _ -> failwith "json: not a string";;
let tisa_json_int = function Tjnum s -> int_of_string s | _ -> failwith "json: not a number";;
let tisa_json_arr = function Tjarr l -> l | _ -> failwith "json: not an array";;

let tisa_read_file f =
  let ic = open_in_bin f in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s;;

(* (name, program, hex, spans) for the named programs (all when names = []).
   Spans without a statement path (wrapper and handlers) get "-". *)
let tisa_v2_images file names =
  let j = tisa_json_parse (tisa_read_file file) in
  if tisa_json_str (tisa_json_field j "schema") <> "tisa-x86-p1-programs-v2"
  then failwith "tisa_v2_images: not a tisa-x86-p1-programs-v2 export";
  mapfilter (fun p ->
      let name = tisa_json_str (tisa_json_field p "program_name") in
      if names <> [] && not (mem name names) then failwith "skip" else
      let prog = parse_term (tisa_json_str (tisa_json_field p "program_hol")) in
      let img = tisa_json_field p "image" in
      let spans = map (fun sp ->
          (tisa_json_int (tisa_json_field sp "offset"), tisa_json_int (tisa_json_field sp "length"),
           tisa_json_str (tisa_json_field sp "template"),
           (match sp with Tjobj l when can (assoc "path") l -> tisa_json_str (assoc "path" l) | _ -> "-")))
        (tisa_json_arr (tisa_json_field img "spans")) in
      (name, prog, tisa_json_str (tisa_json_field img "bytes_hex"), spans))
    (tisa_json_arr (tisa_json_field j "programs"));;
