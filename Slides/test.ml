type ones = 
  | HOLE
  | One of ones

type 'color t =
  | Null : [`green] t
  | Zero : ones * [< `green | `red] t -> [`green] t
  | One  : ones * [< `green | `red] t -> [`yellow] t
  | Two  : ones * [< `green]        t -> [`red] t

type nat = T : [< `green | `yellow] t -> nat