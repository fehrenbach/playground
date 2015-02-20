let foo l =
  let p = ref 1 in
  let z = ref 0 in
  List.iter (fun x -> if x = 0 then z := !z+1 else p := !p*x) l;
  List.map  (fun x -> if x = 0 then (if !z >= 2 then 0 else !p)
                      else (if !z >= 1 then 0 else !p/x)) l;;

let foo2 l =
  let makeMult = fun () -> let p = ref 1 in
                           let f = fun x -> let r = !p
                                            in p := r*x; r in
                           f in
  let fromLeft =  List.map     (makeMult ())           l  in
  let fromRight = List.rev_map (makeMult ()) (List.rev l) in
  List.map2 ( * ) fromLeft fromRight;;

let foo3 a =
  let r = Array.make (Array.length a) 0 in
  let rec loopFromLeft i p =
    if i = Array.length a then ()
    else (r.(i) <- p;
          loopFromLeft (i+1) (p * a.(i))) in
  let rec loopFromRight i p =
    if i < 0 then r
    else (r.(i) <- r.(i) * p;
          loopFromRight (i-1) (p*a.(i))) in
  loopFromLeft 0 1;
  loopFromRight ((Array.length a)-1) 1;;

(* Large numbers or long lists and overflows? Long lists and stack overflows. The list versions should not stack overflow because map is "tail recursive modulo cons", but I guess the ocaml interpreter does not know that... *)


let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
    fx;;

let rl n b =
  Random.init 42;
  Array.to_list (Array.init n (fun _ -> Random.int b));;

let rlnz n b =
  Random.init 42;
  Array.to_list (Array.init n (fun _ -> (Random.int b) + 1));;
