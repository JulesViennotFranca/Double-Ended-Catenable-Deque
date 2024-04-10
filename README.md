# Double-Ended-Catenable-Deque

## Slides

The `Slides` folder contains the first step to understand the whole structure. It describes a way to efficiently store number and list in binary form in order to add 1 or a new element in constant time.

All practical information are written in `explanations.md`.

Furthermore, coq proofs are provided to ensure correctness of such a structure. It is recommanded to first look at the numbers proofs, then the lists ones as they mimic them. Numbers proofs should be looked in this order:

                   correct_number_00.v
                     /             \
                    /               \
       correct_number_10.v      correct_number_01.v
       correct_number_10'.v

- `correct_number_00.v`: Initially, implementations of ensure_green and succ are provided, followed by the proof of lemmas to ensure their correctness.
- `correct_number_10.v`: A type class called NatRep is introduced, which represents structures containing integers. It includes a function called value that retrieves the integer stored in the structure. Consequently, this trait can be extended to packets, colored_nbr, and nbr.
- `correct_number_10'.v`: Similar to the previous proof, but instead of a single type class encompassing all integer-storing structures, we now have two. We retain NatRep and introduce DecoratedNatRep, a type class for structures representing integers decorated with additional types. This distinction proves useful for types like packets or colored_nbr, which include extra arguments such as color. It assists Coq in selecting the correct instances during proofs.
- `correct_number_01.v`: Rather than defining ensure_green and succ separately and then proving their correctness, these two processes are merged. The resulting output is accompanied by a proof of correctness using the dependent type sig.

Thus, we can identify the following behaviors desired for our final code: either implementing functions and then proving their correctness or directly declaring them with a proof of correctness ; deciding whether to use a type class to describe structures or not.
