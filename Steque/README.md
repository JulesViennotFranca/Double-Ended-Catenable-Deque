# Catenable Steque

A *steque* is the name of a *dequeue* without the *eject* operation. In the following, catenable *steques* will be called *steques* for simplicity purpose. When a *steque* is non-catenable, it will be specified.

## Structure description

### Goal

The goal of this structure is to support *push*, *pop* and *inject* operations in constant time, and a *concat* operation in constant time.

### Buffers

In this structure, *buffers* are also used as *prefixes* and *suffixes*. However, this time a buffer is just a non-catenable *steque* with no upper bound on its size. We can use the *deque* structure we implemented to represent them. Also, we require each prefix to contain **at least two elements**.

### Pairs

Contrarly to the *deque* structure, a pair over a set A is not an element of A x A. Now they are defined recursively as:

- a prefix *buffer* of elements of A;
- a possibly empty *steque* of *pairs* over A.

### Steque

Finally, a non-empty *steque s* is defined as either a suffix *suffix(s)* over A, either a triple of prefix *prefix(s)* over A, a child steque *child(s)* over *pairs* of A, and a suffix *suffix(s)* over A.

### Coloration

In this structure, we also have a coloration: *prefix* are given a color based on the number of elements they have. A red *prefix* contains 2 elements, a yellow *prefix* contains 3 elements and a green *prefix* contains more than 4 elements.

Each non-empty *steque* has the color of its prefix if it has one, otherwise it is green.

### Regularity

A *steque* s is *semiregular* if, between any pair of red *steques* in a descendent sequence within s, there is a green *steque* (ignoring intervening yellows).

A *steque* is *regulare* if it is *semiregular* and the first non-yellow *steque* in child(1, s), child(2, s), child(3, s), ... if any, is green.

Notice that if s is *regular*, then child(s) is *semiregular*, and if s is *semiregular*, a *steque* having a green prefix and s as its child *steque* is *regular*.

### Link with previous approaches

Like before, the invariant that any top-level *steque* is *regular* must be maintained. As in previous work, each descendant sequence is represented as a stack of *packets*. A *packet* being a subsequence beginning with the first *steque* or a non-yellow *steque*, and containing all consecutively following yellow *steques*.

### Operations

- *push* and *inject* are simple:
  - *inject*: inject in suffix(s);
  - *push*: if s is a triple, push in prefix(s), if s is a suffix, push in suffix(s);
- *concat* s1 and s2 to form s3:
  - **case 1** - s1 is a triple:
    - if suffix(s1) contains at least two elements, inject the pair (suffix(s1), $\emptyset$) into child(s1),
    - otherwise, if there is an element in s1, push it onto s2,
    - if s2 is a triple, inject (prefix(s2), child(s2)) into child(s1),
    - s3 is the triple (prefix(s1), child(s1), suffix(s2)).
  - **case 2** - s1 is a suffix and s2 is a triple:
    - if |suffix(s1)| ≥ 4, push the pair (prefix(s2), $\emptyset$) onto child(s2) and s3 is the triple (suffix(s1), child(s2), suffix(s2));
    - otherwise, pop elements of suffix(s1), and push them in the right order onto prefix(s2), s3 is (prefix(s2), child(s2), suffix(s2)).
  - **case 3** - both s1 and s2 are suffixes:
    - if |suffix(s1)| ≥ 4, s3 is simply (suffix(s1), $\emptyset$, suffix(s2));
    - otherwise, pop elements of suffix(s1), and push them in the right order onto prefix(s2), s3 is suffix(s2).
- *pop*:
  - if the *steque* is a suffix, we pop the suffix;
  - otherwise, we pop the prefix, but we might end up with a *semiregular* *steque*. We have to restore the regularity:
    - let s1 be the nearest red descendant *steque* of the top-level *steque*,
    - if child(s1) is empty, pop the two elements of prefix(s1), push them in the right order onto suffix(s1) and represent s1 by its suffix only,
    - if not, pop a pair (p, s2) for child(s1), pop the two elements of prefix(s1), push them in the right order onto p, concatenate s2 and child(s1) to form s3, and replace s1 by the triple (p, s3, suffix(s1)).
