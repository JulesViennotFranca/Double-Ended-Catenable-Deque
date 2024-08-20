open Operations
open D
open Datatypes

let init n f = 
  let rec aux accu = function 
    | 0 -> accu 
    | n -> aux (f n :: accu) (n - 1)
  in aux [] n

let deque_of_list_push = 
  let rec aux accu = function
    | [] -> accu 
    | x :: l -> aux (push x accu) l 
  in aux empty

let deque_of_list_inject = 
  let rec aux accu = function
    | [] -> accu 
    | x :: l -> aux (inject accu x) l 
  in aux empty

let () =
  print_endline "CONCATENATION:";

  let steps = 1000 in
  for size = 0 to 500 do
    let lst = init size (fun i -> i) in
    let deck = deque_of_list_push lst in 
    Printf.printf "SIZE: %i --->   " size ;

    let tlist0 = Unix.gettimeofday () in
    for _ = 0 to steps do
      let _ = lst @ lst in
      ()
    done ;
    let tlist1 = Unix.gettimeofday () in
    Printf.printf "list: %f   ---   " (tlist1 -. tlist0) ;

    let tdeque0 = Unix.gettimeofday () in
    for _ = 0 to steps do
      let _ = concat deck deck in
      ()
    done ;
    let tdeque1 = Unix.gettimeofday () in
    Printf.printf "deque: %f   ---   " (tdeque1 -. tdeque0) ;

    let r = (tdeque1 -. tdeque0) /. (tlist1 -. tlist0) in 
    Printf.printf "ratio: %f\n" r;
  done

let sum_list = 
  let rec aux accu = function
    | [] -> accu 
    | x :: l -> aux (x + accu) l 
  in aux 0 

let sum_pop = 
  let rec aux accu d = match pop d with 
    | None -> accu
    | Some (Coq_pair (x, d)) -> aux (x + accu) d 
  in aux 0

let sum_eject =
  let rec aux accu d = match eject d with 
    | None -> accu 
    | Some (Coq_pair (d, x)) -> aux (x + accu) d 
  in aux 0

let () = 
  print_endline "PUSH-POP-INJECT-EJECT:";
  
  let tmake0 = Unix.gettimeofday () in 
  let lst = init 10_000 (fun i -> i) in 
  let tmake1 = Unix.gettimeofday () in 
  let deckp = deque_of_list_push lst in 
  let tmake2 = Unix.gettimeofday () in 
  let decki = deque_of_list_inject lst in 
  let tmake3 = Unix.gettimeofday () in
  Printf.printf "MAKE --->   list %f   ---   push %f   ---   inject %f\n" 
    (tmake1 -. tmake0) (tmake2 -. tmake1) (tmake3 -. tmake2); 

  let tsum0 = Unix.gettimeofday () in
  let s1 = sum_list lst in 
  let tsum1 = Unix.gettimeofday () in 
  let s2 = sum_pop deckp in 
  let tsum2 = Unix.gettimeofday () in 
  let s3 = sum_eject decki in 
  let tsum3 = Unix.gettimeofday () in 
  assert (s1 = s2);
  assert (s2 = s3);
  Printf.printf "SUM --->   list %f   ---   pop %f   ---   eject %f\n"
    (tsum1 -. tsum0) (tsum2 -. tsum1) (tsum3 -. tsum2)