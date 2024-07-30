module type SDEQUE = sig
  type 'a deque
  val empty : 'a deque
  val push : 'a -> 'a deque -> 'a deque
  val pop : 'a deque -> ('a * 'a deque) option
end

let bench name f =
  let t0 = Unix.gettimeofday () in
  let result = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%20s : %.6f s\n%!" name (t1 -. t0) ;
  result

module L = struct
  type 'a deque = 'a list
  let empty = []
  let push x xs = x::xs
  let inject xs x = xs @ [x]
  let pop = function
    | [] -> None
    | x::xs -> Some (x, xs)
  let rec eject = function
    | [] -> None
    | x::xs -> match eject xs with
      | None -> Some ([], x)
      | Some (xs, y) -> Some (x::xs, y)
  let concat = ( @ )
end

module Deq = struct
  include Deq.Core

  let push = dpush
  let pop = dpop
  let empty = dempty
end

module TestS (D : SDEQUE) = struct

  let make n =
    let rec go acc i =
      if i = 0
      then acc
      else go (D.push i acc) (i - 1)
    in
    go D.empty n

  let rec depop xs =
    match D.pop xs with
    | None -> ()
    | Some (_, xs) -> depop xs

  let () =
    let xs = bench "make 10m w push" (fun () -> make 10_000_000) in
    bench "empty w pop" (fun () -> depop xs)

end

let () = Printf.printf "-- List -------------------\n%!"
module A = TestS (L)
let () = Printf.printf "\n%!"

let () = Printf.printf "-- Struct1 ----------------\n%!"
module B = TestS (Sdeque.Core)
let () = Printf.printf "\n%!"

let () = Printf.printf "-- Deq --------------------\n%!"
module C = TestS (Deq)
let () = Printf.printf "\n%!"

let () = Printf.printf "-- Struct3 ----------------\n%!"
module D = TestS (Cdeque.Core)
let () = Printf.printf "\n%!"

let () = Printf.printf "-- Deque ------------------\n%!"
module E = TestS (Deque.Core)
let () = Printf.printf "\n%!"

let () = Printf.printf "-- Concatenation ----------\n%!"
module TestC = struct

  let make empty inject n =
    let rec go acc i =
      if i = 0
      then acc
      else go (inject acc i) (i - 1)
    in
    go empty n

  let rec empty eject xs =
    match eject xs with
    | None -> ()
    | Some (xs, _) -> empty eject xs

  let concat ct d =
    let steps = 1000 in
    for _ = 0 to steps do
      let _ = ct d d in ()
    done

  let bench_size size =
    Printf.printf "size: %i\n" size;
    Printf.printf "%s :\n" "make size w inject";
    let l = bench "list"
            (fun () -> make [] L.inject size) in
    let s = bench "struct3"
            (fun () -> make Cdeque.Core.empty Cdeque.Core.inject size) in
    let d = bench "deque"
            (fun () -> make Deque.Core.empty Deque.Core.inject size) in
    Printf.printf "%s :\n" "concat";
    bench "list" (fun () -> concat L.concat l);
    bench "struct3" (fun () -> concat Cdeque.Core.concat s);
    bench "deque" (fun () -> concat Deque.Core.concat d);
    Printf.printf "%s :\n" "empty w eject";
    bench "list" (fun () -> empty L.eject l);
    bench "struct" (fun () -> empty Cdeque.Core.eject s);
    bench "deque" (fun () -> empty Deque.Core.eject d)

  let () =
    for size = 0 to 200 do
      bench_size size
    done;
    bench_size 10000

end
let () = Printf.printf "\n%!"