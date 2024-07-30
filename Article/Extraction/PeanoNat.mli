open Datatypes

module Nat :
 sig
  val pred : nat -> nat

  val sub : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1
 end
