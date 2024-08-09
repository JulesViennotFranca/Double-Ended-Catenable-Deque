# Compte rendu 1

Bonjour, voici un compte rendu pour vous tenir au courant de mon travail depuis la dernière fois.

## La définition des différentes structures

Premièrement, voici la tête qu'aurait les types dont nous avons besoin pour la deuxième structure :

```Coq
(* A relation between the packet, the following steque and the current steque
   colors. *)

Inductive csteque_color : color -> color -> color -> Type :=
  | CCGreen {G R} : csteque_color green (Mix G NoYellow R) green
  | CCYellow : csteque_color yellow green yellow
  | CCOrange : csteque_color yellow red orange
  | CCRed : csteque_color red green red.

(* The mutally recursive definition of elements, packets and colored steque.

   Elements represents the types of elements stored. At level 0, elements of
   type A are stored. When the level increase, elements of the new level are
   made of a prefix of elements of the previous level and a colored steque of
   the new level. *)

Inductive element (A : Type) : nat -> Type :=
  | ZElt : A -> element A 0
  | SElt {lvl : nat} {C1 C2 : color} :
      prefix' (element A lvl) C1 ->
      lvl_csteque A (S lvl) C2 ->
      element A (S lvl)

   (* Packets represents the same concept as before : either a Hole, the end of
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with lvl_packet (A : Type) : nat -> nat -> color -> Type :=
  | Hole {lvl : nat} : lvl_packet A lvl 0 uncolored
  | Triple {lvl len : nat} {Y : yellow_hue} {C : color} :
      prefix' (element A lvl) C ->
      lvl_packet A (S lvl) len (Mix NoGreen Y NoRed) ->
      suffix' (element A lvl) ->
      lvl_packet A lvl (S len) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a
   following colored steque. *)

with lvl_csteque (A : Type) : nat -> color -> Type :=
  | Small {lvl : nat} :
      suffix' (element A lvl) ->
      lvl_csteque A lvl green
  | Big {lvl len nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len C1 ->
      lvl_csteque A nlvl C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl C3.
```

## Comment avoir la séquence qu'elles représentent ?

J'ai du mal à écrire une fonction qui renvoie la liste associée à nos différentes structures. En effet, la preuve qu'une telle fonction termine n'est pas triviale, et Coq n'arrive pas à l'inférer tout seul : je suppose que c'est à cause des appels récursifs sur des listes en utilisant map. La fonction qui ne marche pas aurait cette forme :

```Coq
Equations element_seq {A lvl} : element A lvl -> list A :=
element_seq (ZElt a) := [a];
element_seq (SElt p cs) :=
    concat (map element_seq (prefix'_seq p)) ++
    csteque_seq cs

with packet_left_seq {A lvl len C} : lvl_packet A lvl len C -> list A :=
packet_left_seq Hole := [];
packet_left_seq (Triple p pkt _) :=
    concat (map element_seq (prefix'_seq p)) ++
    packet_left_seq pkt

with packet_right_seq {A lvl len C} : lvl_packet A lvl len C -> list A :=
packet_right_seq Hole := [];
packet_right_seq (Triple _ pkt s) :=
    packet_right_seq pkt ++
    concat (map element_seq (suffix'_seq s))

with csteque_seq {A lvl C} : lvl_csteque A lvl C -> list A :=
csteque_seq (Small s) :=
    concat (map element_seq (suffix'_seq s));
csteque_seq (Big pkt cs eq_refl _) :=
    packet_left_seq pkt ++
    csteque_seq cs ++
    packet_right_seq pkt.
```

ou

```Coq
Equations structure_seq (k : seq_kind) {A lvl len C}
    (s : seq_struct k A lvl len C) : list A :=
structure_seq Element (ZElt a) := [a];
structure_seq Element (SElt p cs) :=
    concat (map (structure_seq Element) (prefix_seq p)) ++
    structure_seq CSteque cs;
structure_seq FPacket Hole := [];
structure_seq FPacket (Triple p pkt _) :=
    concat (map (structure_seq Element) (prefix_seq p)) ++
    structure_seq FPacket pkt;
structure_seq RPacket Hole := [];
structure_seq RPacket (Triple _ pkt s) :=
    structure_seq RPacket pkt ++
    concat (map (structure_seq Element) (suffix_seq s));
structure_seq CSteque (Small s) :=
    concat (map (structure_seq Element) (suffix_seq s));
structure_seq CSteque (Big pkt cs eq_refl _) :=
    structure_seq FPacket pkt ++
    structure_seq CSteque cs ++
    structure_seq RPacket pkt.
```

Comme notre première structure apparaît dans les prefixes et les suffixes, je vois mal comment on pourrait éviter de faire un map sans re-écrire le code de la première structure.
J'ai donc réfléchi à plusieurs solutions pour résoudre ce problème.

## Solution 1 : ajouter un fuel à notre fonction qui donne la liste

On rajoute un argument de fuel à notre fonction structure_seq qui décroit à chaque appel récursif, quand le fuel est nul, on renvoie simplement la liste vide. La nouvelle fonction s'écrit alors :

```Coq
Equations fueled_element_seq {A lvl} (fuel : nat) : element A lvl -> list A :=
fueled_element_seq 0 _ := [];
fueled_element_seq (S _) (ZElt a) := [a];
fueled_element_seq (S fuel) (SElt p cs) :=
    concat (map (fueled_element_seq fuel) (prefix'_seq p)) ++
    fueled_csteque_seq fuel cs

with fueled_packet_left_seq {A lvl len C} (fuel : nat) : lvl_packet A lvl len C -> list A :=
fueled_packet_left_seq 0 _ := [];
fueled_packet_left_seq (S _) Hole := [];
fueled_packet_left_seq (S fuel) (Triple p pkt _) :=
    concat (map (fueled_element_seq fuel) (prefix'_seq p)) ++
    fueled_packet_left_seq fuel pkt

with fueled_packet_right_seq {A lvl len C} (fuel : nat) : lvl_packet A lvl len C -> list A :=
fueled_packet_right_seq 0 _ := [];
fueled_packet_right_seq (S _) Hole := [];
fueled_packet_right_seq (S fuel) (Triple _ pkt s) :=
    fueled_packet_right_seq fuel pkt ++
    concat (map (fueled_element_seq fuel) (suffix'_seq s))

with fueled_csteque_seq {A lvl C} (fuel : nat) : lvl_csteque A lvl C -> list A :=
fueled_csteque_seq 0 _ := [];
fueled_csteque_seq (S fuel) (Small s) :=
    concat (map (fueled_element_seq fuel) (suffix'_seq s));
fueled_csteque_seq (S fuel) (Big pkt cs eq_refl _) :=
    fueled_packet_left_seq fuel pkt ++
    fueled_csteque_seq fuel cs ++
    fueled_packet_right_seq fuel pkt.
```

Pour la suite de la preuve, on ne manipulerait plus directement nos structures mais leur version "fueled" : notre structure `s`, un `fuel` pour la fonction structure_seq et une preuve qu'on a assez de fuel pour calculer la liste (quelque chose comme `forall n : nat, fuel <= n -> fueled_structure_seq fuel s = fueled_structure_seq n s`).

Cela serait une solution assez simple, mais peut satisfaisante comme on ne manipule pas nos types directement. De plus, les preuves serait sûrement assez longue comme il faudrait en plus prouver que l'on a assez de fuel.

## Solution 2 : ajouter une notion de profondeur à nos structure

Pour éviter d'avoir à prouver que l'on a assez de fuel, on pourrait rentrer directement notre fuel dans nos types. Ainsi, on rajouterait un paramètre de *profondeur* à nos types pour tenir compte de leur profondeur maximale, et donc du fuel qu'il faudrait.

Pour pouvoir avoir un paramètre de profondeur efficace, comme les différentes structures sont amenées à être modifiées dans nos fonctions, `s : structure A depth` veut dire que `s` est une `structure A` (les autres paramètres sont omis) de profondeur inférieure à `depth`.

Cette solution nous permettrait d'avoir des preuves plus compactes et de manipuler nos types directement, mais elle alourdit considérablement la définition de nos structures :

```Coq
Inductive element (A : Type) : nat -> nat -> Type :=
  | ZElt : A -> element A 0 0
  | SElt {lvl pdpt csdpt dpt : nat} {C1 C2 : color} :
      prefix' (element A lvl pdpt) C1 ->
      pdpt <= dpt ->
      lvl_csteque A (S lvl) csdpt C2 ->
      csdpt <= dpt ->
      element A (S lvl) (S dpt)

with lvl_packet (A : Type) : nat -> nat -> nat -> color -> Type :=
  | Hole {lvl : nat} : lvl_packet A lvl 0 0 uncolored
  | Triple {lvl len pdpt pktdpt sdpt dpt : nat} {Y : yellow_hue} {C : color} :
      prefix' (element A lvl pdpt) C ->
      pdpt <= dpt ->
      lvl_packet A (S lvl) len pktdpt (Mix NoGreen Y NoRed) ->
      pktdpt <= dpt ->
      suffix' (element A lvl sdpt) ->
      sdpt <= dpt ->
      lvl_packet A lvl (S len) (S dpt) C

with lvl_csteque (A : Type) : nat -> nat -> color -> Type :=
  | Small {lvl sdpt dpt : nat} :
      suffix' (element A lvl sdpt) ->
      sdpt <= dpt ->
      lvl_csteque A lvl (S dpt) green
  | Big {lvl len pdpt ndpt dpt nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len pdpt C1 ->
      pdpt <= dpt ->
      lvl_csteque A nlvl ndpt C2 ->
      nlvl = len + lvl ->
      len + ndpt <= dpt ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl (S dpt) C3.
```

Je suis conscient que la définition pourrait être allégée en utilisant `dpt` dans les appels récursifs et `S dpt` dans les définitions. Pour cela, il faudrait une fonction `lift : dpt <=dpt' -> structure A dpt -> structure A dpt'` qui doit être faisable. Cependant, avec une telle fonction, on ne pourrait pas revenir en arrière, ce qui pourrait poser problème avec les preuves. Je préfère donc garder une définition plus générale pour l'instant. On a alors une nouvelle version de la fonction pour obtenir la séquence associée à une structure :

```Coq
Equations structure_seq (k : seq_kind) {A lvl len dpt C}
    (s : seq_struct k A lvl len dpt C) : list A by wf dpt :=
structure_seq Element (ZElt a) := [a];
structure_seq Element (SElt p _ cs _) :=
    map_concat (fun elt => structure_seq Element elt) (prefix'_seq p) ++
    structure_seq CSteque cs;
structure_seq FPacket Hole := [];
structure_seq FPacket (Triple p _ pkt _ _ _) :=
    map_concat (fun elt => structure_seq Element elt) (prefix'_seq p) ++
    structure_seq FPacket pkt;
structure_seq RPacket Hole := [];
structure_seq RPacket (Triple _ _ pkt _ s _) :=
    structure_seq RPacket pkt ++
    map_concat (fun elt => structure_seq Element elt) (suffix'_seq s);
structure_seq CSteque (Small s) :=
    map_concat (fun elt => structure_seq Element elt) (suffix'_seq s);
structure_seq CSteque (Big pkt _ cs eq_refl _ _) :=
    structure_seq FPacket pkt ++
    structure_seq CSteque cs ++
    structure_seq RPacket pkt.
```

## Solution 3 : définir un ordre bien fondé pour notre définition mutuellement récursive

La dernière solution que j'explore en ce moment est de définir un ordre bien fondé pour notre définition mutuellement récursive. Il faudrait pouvoir préciser un ordre sur nos structure. Pour cela, je pensais utiliser un type

```Coq
Inductive kind : Type := Element | Packet | Csteque.
```

ainsi que deux entiers naturels : `lvl` et `len`.

Le nom du deuxième paramètre len est un peu trompeur, pour les `packet`, il s'agirait effectivement de `len`. Mais pour les `element` et les `csteque`, il s'agirait d'un paramètre qui aiderait à définir l'ordre. On peut alors spécifier les règles que l'on veut pour notre ordre avec les différents appels récursifs de notre fonction :

- Element lvl ? < Element (S lvl) ?
- la comparaison entre Packet ? ? et Element ? ? n'arrive pas
- Csteque (S lvl) ? < Element (S lvl) ?
- Element lvl ? < Packet lvl (S len)
- Packet (S lvl) len < Packet lvl (S len)
- la comparaison entre Csteque ? ? et Packet ? ? n'arrive pas
- Element lvl ? < Csteque lvl ? mais possiblement transformable en
  - Element lvl ? < Csteque (S lvl) ?
  - Csteque (S lvl) ? < Csteque (S lvl) ?
- Packet lvl len < Csteque lvl ?
- Csteque (len + lvl) ? < Csteque lvl ?

Tout l'enjeux est de trouver par quoi remplacer les points d'intérogation pour avoir le bon ordre sur nos éléments. C'est ce que je suis en train de chercher en ce moment.

Nouvelle idée : s'affranchir de packet_seq en utilisant le fait qu'une csteque peut être vue comme un suffix ou un triplet prefix - enfant - suffix. Il ne faut alors plus qu'une relation sur Element et Csteque.

- Element lvl ? < Element (S lvl) ?
- Csteque (S lvl) ? < Element (S lvl) ?
- Element lvl ? < Csteque lvl ?
- Csteque (S lvl) ? < Csteque lvl ?

Pour la définition d'un ordre bien fondé, comme une même structure peut se retrouver récursivement dans elle-même, le seul paramètre dont on peut être sûr qu'il décroit serait similaire à notre paramètre `dpt` précédent.
