# Double Ended Catenable Deque

We will name them *deque* in the following. If we use a non-catenable *deque*, it will be specified.

## Structure description

### Goal

The goal of this structure is to support every operation, *push*, *pop*, *inject*, *eject* and *concat*, in constant time.

### Buffers

As for *steques*, we also use two kinds of buffers, *prefixes* and *suffixes*, made of non-contenable *deques*.

### Triples

*Triples* over a set A are defined recursively as a *prefix* over A, a *deque* of *triples* over A and a *suffix* over A. Triples in the *deque* are called *stored triples*.

### Deques

A non-empty *deque* over A is represented as either one *triple* over A, called an *only triple*, or an ordered pair of triples over A, called a *left triple* and a *right triple*. The *deques* in each *triple* are represented the same way.

### Children relation

If t = (prefix, deque, suffix) with deque $\neq \empty$, the children of t are the one or two *triples* that make up deque.

### Constrains

We have now 4 kinds of triples, *stored*, *only*, *left* and *right* ones. For each kind, we require special constrains. Let (p, d, s) be a triple, if it is a

- *stored triple*: p and s both need to have at least 3 elements, unless d and one of the buffer are empty, in which case the remaining buffer must contain at least 3 elements;
- *only triple*: p and s both need to have at least 5 elements, unless d and one of the buffer are empty, in which case the remaining buffer must contain 1 element or more;
- *left triple*: p must contain at least 5 elements, and s exactly 2;
- *right triple*: s must contain at least 5 elements, and p exactly 2.

### Coloration

The color associated to *triples* also vary according to its kind. Let (p, d, s) be a triple, its color is:

- *stored triple*: green;
- *only triple*:
  - d = $\empty$: green;
  - p and s contain at least 8 elements: green;
  - p or s contains 7 elements and the other at least 7: yellow;
  - p or s contains 6 elements and the other at least 6: orange;
  - p or s contains 5 elements and the other at least 5: red;
- *left triple*:
  - d = $\empty$: green;
  - p contains at least 8 elements: green;
  - p contains 7 elements: yellow;
  - p contains 6 elements: orange;
  - p contains 5 elements: red;
- *right triple*:
  - d = $\empty$: green;
  - s contains at least 8 elements: green;
  - s contains 7 elements: yellow;
  - s contains 6 elements: orange;
  - s contains 5 elements: red;

### Preferred paths

In our previous structures, the notion of *packets* served to represent lists of consecutive yellow *steques* or non-catenable *deques*. But here, our new definition for *deque* has more of a tree shape, we need a new way of representing those consecutive yellow, and now orange, triples. Hence, the notion of *preferred paths* is introduced.

Each yellow and orange *triple* has a *preferred child*. When there is an only child, it is obviously the preferred one, otherwise, yellow *triples* prefer the left child, orange ones the right child.

The preferred children relation defines *preferred paths*. They start at *triples* that are not preferred children, and pass through successive preferred children until reaching a triple without preferred children.

Thus, each *preferred path* consists of a sequence of zero or more yellow or orange *triples* followed by a green or red *triple*.
Each *preferred path* is then assigned the color of its last *triple*.

### Regularity

The notion of *regularity* is adapted to our tree shaped structure with 4 colors.

A *deque* is *semiregular* if both of the following conditions holds:

- every *preferred path* that starts at a child of a red triple is a green path;
- every *preferred path* that starts at a non-preferred child of an orange triple is a green path.

Finally, a *deque* is *regular* if it is *semiregular* and each preferred path that starts at a top-level *triple* is green.

The invariant that the top-level *deque* is *regular* must be maintained.

### Compressed forest

As for *packets* in our previous structures, *preferred paths* must be shortcuted in order to have an efficient computation. Thus, a representation for *deques* enabling this behaviour is needed.

To this end, the notion of *adoption* is introduced. The *adoption* relation links the first and last *triples* of *preferred paths* of at least three *triples* (enough for *adoption* to be meaningful). We call such a first *triple* the *adoptive parent* of the last *triple*, called the *adoptive child*.

The *compressed forest* is defined by the parent-child relation on triples, except that each *adopted child* is a child of its *adoptive parent*. In the *compressed forest* form, a triple has at most three children, one of which may be adopted.

*Deques* are now represented by their *compressed forest* form, with a node for each triple containing the prefix, the suffix, and pointers to the nodes representing its child *triples*.

### Push and inject

The *push* and *inject* operations are symmetric.

Let d be a *deque* on which we wish to *push* an element. If d is empty, we simply create an *only triple* with one non-empty buffer containing our element. If d is non-empty, let t = (pl, dl, sl) be its *left triple* or *only triple*. If pl is non-emty, we *push* the element onto pl, otherwise, we *push* it on sl.

### Concat

Let d and e be the two *deques* we want to concatenate. They are supposed non-empty, otherwise the concatenation is trivial. The concatenation of d and e then follows one of the 4 cases:

- all buffers at top-level of d and e are non-empty. The new deque will consist of two *triples* t and u, with t formed from the top-level *triples* of d, and u formed from the top-level *triples* of e. 4 subcases arrise for the formation of t (the formation of u from e is symmetric):
  - d is made of two *triples* t1 = (p1, d1, s1) and t2 = (p2, d2, s2) with d1 $\neq \empty$. Combine s1 and p2 into a single buffer p3. Eject the last 2 elements from s2 and add them to a new buffer s3, with s2' the remaining buffer. Inject (p3, d2, s2') in d1 to form d1'. Let t = (p1, d1', s3).
  - d is made of two *triples* t1 = (p1, $\empty$, s1) and t2 = (p2, d2, s2). Inject elements from s1 and p2 onto p1 to form p1'. Replace the representation of d by (p1', d2, s2) and apply the corresponding following subcase.
  - d is made of one *triple* t1 = (p1, d1, s1) with d1 $\neq \empty$. Eject the last two elements of s1 and add them to a new buffer s2, with s1' the remaining buffer. Inject ($\empty$, $\empty$, s1') onto d1 to form d1'. Let t = (p1, d1', s2).
  - d is made of one *triple* t1 = (p1, $\empty$, s1). If s1 has less than 8 elements, move all of them except the last 2 onto p1 to form p1' and s1', let t = (p1', $\empty$, s1'). Otherwise, move the first 3 elements of s1 onto p1 to form p1', move the last 2 elements of s1 into a new buffer s2, forming s1'. Push ($\empty$, $\empty$, s1') onto an empty deque to form d2. Let t = (p1', d2, s2).
- d is made of an only *triple* t1 = (p1, d1, s1) with only one non-empty buffer, and all buffers at top-level of e are non-empty. Let t2 = (p2, d2, s2) be the *left triple* or *only triple* of e. Let p3 be the non-empty buffer of p1 and s1, if p3 contains less then 8 elements, push all these onto p2 to form p2', and let t3 = (p2', d2, s2). Otherwise, push (p2, $\empty$, $\empty$) onto d2 to form d2', let t3 = (p3, d2', s2). t3 is the *left triple* or *only triple* of the new deque.
- e is made of an *only triple* with only one non-empty buffer, and all buffers at top-level of d are non-empty. This case is symmetric to the previous one.
- d and e are made of *only triples* with a single non-empty buffer. Let p be the non-empty buffer of d and s the one of e. If either p or s contains less than 8 elements, combine them into a single buffer b and let t = (b, $\empty$, $\empty$). Otherwise, let t = (p, $\empty$, s).

### Pop and eject

The *pop* and *eject* operations are symmetric.

Operations *pop* consists of 2 parts. The first one removes the element to be popped, and the second one repairs the damage done.

First, let t be the *left triple* or *only triple* of the *deque* d to be popped. We *pop* from the prefix of t, or from the suffix if the prefix is empty, resulting in a *triple* t'. t is replaced by t' in d, forming the *deque* d'. d' may not be regular but only *semiregular* because the *preferred path* starting at t' may be red. In this case, last red *triple* of this path is denoted u (it can be accessed in constant time through the *compressed forest* form). Now, u and its descendant will be replaced by a tree of *triples* representing the same elements but with a green root v. The new *deque* will be regular and the invariant will be preserved.

Let u = (p1, d1, s1) with d1 $\neq \empty$ because u is red, to repair it, the corresponding of the following cases is applied:

- u is a *left triple*, pop the first *triple* (p2, d2, s2) from d1 (without any repair), forming d1',
  - if both p2 and s2 are non-empty, push ($\empty$, $\empty$, s2) onto d1' to form d1''. Push the elements from p1 onto p2, forming p2'. Concatenate *deques* d2 and d1'' to form d3. Let v = (p2', d3, s1).
  - one of p2 and s2 is empty, combine p1, p2 and s2 into a single buffer p3, let v = (p3, d1', s1).
- u is an *only triple*:
  - if s1 contains at least 8 elements, proceed as in the first case, obtaining v = (p4, d4, s1), p4 containing at least 8 elements.
  - if p1 contains at least 8 elements, procedd symmetrically to the first case, obtaining v = (p1, d4, s4), s4 containing at least 8 elements.
  - p1 and s1 contains at most 7 elements, pop the first *triple* (p2, d2, s2) from d1 (without any repair) forming d1'.
    - if d1 = $\empty$, combine p1 and p2 in p4, s1 and s2 in s4, v = (p4, d2, s4).
    - otherwise, eject (p3, d3, s3) from d1' (without any repair) forming d1''.
      - if one of p2 or s2 is empty, combine p1, p2 and s2 in p4 and let d4 = d1'';
      - otherwise, push ($\empty$, $\empty$, s2) onto d1'', forming d1''', push the elements of p1 onto p2 to form p4, and concatenate d2 and d1''' to form d4;
      - symmetrically, if one of p3 or s3 is empty, combine p3, s3 and s1 in s4 and let d5 = d4;
      - otherwise, inject (p3, $\empty$, $\empty$) onto d4, forming d4', inject the elements of s1 onto s2 to form s4, and concatenate d4' and d3 to form d5;
      - v = (p4, d5, s4).
