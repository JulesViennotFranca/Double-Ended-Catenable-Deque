# Plan de l'article

## Simple approach

Expliquer le principe du squelette avec des couleurs avec le binary counting
-> comment représenter les nombres pour pouvoir ajouter 1 en temps constant

- expliquer pourquoi on a besoin de la redundant binary representation (0, 1 et 2 comme valeurs de bit) qui amène à avoir 3 couleurs
- présenter le concept de régularité qui permet de pouvoir toujours faire notre opération en temps constant
- montrer l'importance de regrouper les 1 ensembles pour maintenir la régularité efficacement
- remplacer les bits par des couleurs : 0 devient vert, on peut effectuer notre opération sans danger, 1 devient jaune, faire une opération peut mener à un état rouge, 2 devient rouge, on ne peut pas faire notre opération. Exprimer les contraintes de régularité en fonction des couleurs
- s'affranchir des nombres et ne manipuler que des couleurs, les couleurs, leurs significations et la régularité seront les mêmes dans les première et deuxième structures

## Première structure

base des deux suivantes

### Rappels Kaplan - Tarjan

Le squelette et la régularité fonctionnent comme dans la simple approach, mais la couleur d'un niveau est donné par le nombre d'élément dans ses buffers préfixe et suffixe. Les couleurs ont bien la même signification : vert = faire les opérations sans problèmes, jaune = certaines opérations peuvent mener à un état rouge, rouge = certaines opérations ne peuvent pas être faite

### Copie du code OCaml

Finalement, la preuve vient assez naturellement à partir du code OCaml : on parlerait ici plus de la preuve qu'avait rédigé Armaël

- pour les couleurs, autant ne pas compliquer la lecture et directement présenter notre approche finale pour représenter les couleurs, celle avec 3 bits pour vert jaune et rouge
- on pourait ensuite montrer les types OCaml et dire qu'il se traduise de manière identique en Coq

Parler de notre choix d'utilisation de Equations, hauto, aac_tactic, qui nous permettent d'avoir très peu de preuves à écrire à la main et de bien gérer les égalités de listes

## Deuxieme structure

pas utilisée dans la dernière mais aide à comprendre les principales difficultés rencontrées

### Rapide rappels de Kaplan - Tarjan

- squelette reste similaire
- ajout de récursion : la structure se contient elle-même -> c'est ce qui amène aux deux problèmes principaux rencontrés

### Stricte positivité

Le premier problème rencontrer quand on veut coder les types récursifs de la deuxième structure sont les contraintes de stricte positivité d'OCaml : explications similaires au long mail concernant cela que je vous avais envoyé. Pas possible d'avoir quelque chose de la forme 'a t t dans la définition de t et pas possible d'avoir 'a t qui apparait comme paramètre non-uniforme d'un type inductif (ce concept sera détaillé) dans la définition de t.

Solutions pour les problèmes de récursivité, ajouter un entier naturel dans les paramètres de type, le level, qui rend compte du nombre d'itérations faites sur les éléments contenu dans une structure. Pour notre première structure, il s'agit du nombre d'itérations du produit (lvl 0 = A, lvl 1 = A * A, ...). Pour notre deuxième structure steque, il s'agit du nombre d'itérations de prefix \* steque.

On peut présenter le changement de types dans la première structure.

### Inline de fonction

Un autre problème rencontré à ce stade là est la définition des fonctions séquences (celles qui permettent d'avoir la liste correspondant à nos structures) : des fonctions mutuellements récursives ne permettent pas de les écrire car Coq ne trouve pas d'argument décroissant, alors qu'il s'agit seulement d'une induction sur nos types mutuellement récursifs.

La façon de contourner cette limitation de Coq est de tout inliner en un seul fixpoint, Coq reconnaît alors bien l'induction. Il faut ensuite écrire un lemme permettant de faire le lien entre cette fonction et les fonctions qui l'utilisent ensuite. On rédige aussi une fonction map sur notre première structure.

Finalement, comme la deuxième structure n'est pas utile pour la suite et qu'elle a pour seul but de présenter les problèmes, une autre approche serait de faire des exemples plus simples pour justifier nos modifications sur la première structure.

## Troisième structure

### Dernier rappels Kaplan - Tarjan

D'abord détailler l'évolution du squelette qui à maintenant une forme d'arbre, puis ensuite parler des buffers et des stored triples

### Ajout de la taille

On a besoin d'avoir le nombre d'élément contenu dans notre première structure pour les buffers de la dernière. Mais si on rajoute simplement une taille avec une preuve qu'il s'agit bien du nombre d'élément contenu dans notre première structure, on ne remplit pas les contraintes de stricte positivité requises par Coq.

Une solution est de rentrer cette taille comme paramètre de type pour notre première structure, et de récrire avec ce nouveau paramètre notre première structure.

On peut montrer le nouveau type que cela nous donne.

### Ecriture de la preuve

Après avoir fait toute ces adaptations, l'écriture de la preuve vient assez naturellement, avec une grosse définition de types récursifs et de gros fixpoint avec de nombreuses fonctions inliner qui mettent beaucoup de temps à être validées par Coq.
