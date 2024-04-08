# Double-Ended-Catenable-Deque

## Slides

The `Slides` folder contains the first step to understand the whole structure. It describes a way to efficiently store number and list in binary form in order to add 1 or a new element in constant time.

All practical information are written in `explanations.md`.

Furthermore, coq proofs are provided to ensure correctness of such a structure. It is recommanded to first look at the numbers proofs, then the lists ones as they mimic them. Numbers proofs should be looked in this order:

                correct_number_0.v
                  /            \
                 /              \
    correct_number_00.v     correct_number_01.v

- `correct_number_0.v`: getting integers represented by a packet and integers represented by colored_nbr is done separatly in two different functions. First, an implementation of `ensure_green` and `succ` is given, then lemmas are proved to ensure their correctness.
- `correct_number_00.v`: a type class is added, `NatRepresentation`, which stands for structures representing integers. It contains a unique function value that returns the integer stored in the structure. Thus, the trait can be derived for packet, colored_nbr and nbr, and each of them have a function value that gives back the integer stored.
- `correct_number_01.v`: instead of defining `ensure_green` and `succ` then proving their correctness, the two processes are merged. The result is given along a proof of correctness using the dependent type `sig`.

Hence, we can extract behaviors that we want for our final code:

- implementing then proving our functions, or directly declare them with a proof of correctness;
- having two separate functions for decoding packet and colored_nbr, or having a single function handling colored_nbr;
- if we choose to have two separate functions, having a type class describing structures or not.
