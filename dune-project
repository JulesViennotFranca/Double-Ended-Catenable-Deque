(lang dune 3.8)
(using coq 0.8)
(generate_opam_files true)

(name DECD)
(source (github JulesViennotFrance/Double-Ended-Catenable-Deque))
(license MIT)
(authors "Cambium, Inria")
(maintainers "jules.viennot@inria.fr")
(version 0.1)

(package
  (name DECD)
  (allow_empty)
  (synopsis "Code from Arthur Wendling on Purely Functional, Real-Time Deques with Catenation")
  (depends (ocaml (>= "4.08")))
  (description
    "\
A double-ended queue is an ordered collection for which elements can be \
added and removed from the front and the back. This library provides a \
purely functional implementation, such that the following operations are \
all worst-case constant time:
- `push` adds an element to the front of the deque
- `pop` pops the left-most element
- `inject` adds an element at the back
- `eject` pops the right-most element
- `concat` concatenates two deques
This datastructure was invented by Kaplan and Tarjan.
The OCaml code presented was written by Arthur Wendling at \
https://github.com/art-w/deque/tree/master")
)