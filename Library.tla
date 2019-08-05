------------------------------ MODULE Library ------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, Bags


(***************************************************************************)
(* Value functions                                                         *)
(***************************************************************************)
max(x, y) == IF x>y THEN x ELSE y

min(x, y) == IF x<y THEN x ELSE y


(***************************************************************************)
(* Set functions                                                           *)
(***************************************************************************)
SetNone(S) == CHOOSE x : x \notin S

SetPick(S) == CHOOSE e \in S : TRUE

SetMax(S) == IF S = {} THEN -1
             ELSE CHOOSE i \in S : \A j \in S : i >= j

SetMin(S) == IF S = {} THEN -1
             ELSE CHOOSE i \in S : \A j \in S : i <= j

RECURSIVE SetSum(_)
SetSum(S) == IF S={} THEN 0
             ELSE LET s == CHOOSE x \in S : TRUE
                  IN s + SetSum(S \ {s})

SetSort(S) == LET D == 1..Cardinality(S)
              IN {seq \in [D -> S] : /\ S \subseteq {seq[i] : i \in D}
                                     /\ \A i,j \in D : (i < j) => (seq[i].key <= seq[j].key)}

(***************************************************************************)
(* Bag functions                                                           *)
(***************************************************************************)
BagAdd(B, e) == B (+) [e |-> 1]

BagRemove(B, e) == B (-) [e |-> 1]


(***************************************************************************)
(* Map functions                                                           *)
(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(* The image of a map *)
Image(f) == {f[x] : x \in DOMAIN f}

IsBijection(f, X, Y) == /\  DOMAIN f = X
                        /\  Image(f) = Y
                        /\  \A x,y \in X : x # y => f[x] # f[y]
                        /\  \A y \in Y : \E x \in X : f[x] = y

IsInjective(f) == \A x,y \in DOMAIN f : x # y => f[x] # f[y]


(***************************************************************************)
(* Sequence functions                                                      *)
(***************************************************************************)

(*
SeqMax(S) == IF S = <<>> THEN -1
             ELSE LET i == CHOOSE i \in DOMAIN S : \A j \in DOMAIN S : S[i] >= S[j]
                  IN S[i]
*)

SeqMax(S) == SetMax(Image(S))

SeqMin(S) == SetMin(Image(S))

RECURSIVE SeqSum(_)
SeqSum(S) == IF S = <<>> THEN 0
             ELSE Head(S) + SeqSum(Tail(S))

IsIncreasing(f) == \A x,y \in DOMAIN f : x <= y => f[x] <= f[y]

IsSubSequence(s1, s2) == \E f \in [DOMAIN s1 -> DOMAIN s2] : /\  IsInjective(f)
                                                             /\  IsIncreasing(f)
                                                             /\  \A i \in DOMAIN s1 : s1[i] = s2[f[i]]

\* Sequences with no duplicates:
RECURSIVE NoDupRec(_,_)
NoDupRec(es, seen) == IF es = <<>> THEN TRUE
                      ELSE IF es[1] \in seen THEN FALSE
                           ELSE NoDupRec(Tail(es), seen \cup {es[1]})

NoDup(es) == NoDupRec(es,{})

NoDupSeq(E) == {es \in Seq(E) : NoDup(es)}

\* Removing duplicates from a sequence:
RECURSIVE RemDupRec(_,_)
RemDupRec(es, seen) == IF es = <<>> THEN <<>>
                       ELSE IF es[1] \in seen THEN RemDupRec(Tail(es), seen)
                            ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})
RemDup(es) == RemDupRec(es, {})

\* Sequence prefix:
Prefix(s1,s2) == Len(s1) <= Len(s2) /\  \A i \in DOMAIN s1 : s1[i] = s2[i]

\* The longest common prefix of two sequences:
RECURSIVE LongestCommonPrefixLenRec(_,_,_)
LongestCommonPrefixLenRec(S,n,e1) == IF S = {} THEN 0
                                     ELSE IF /\ \A e \in S : Len(e) >= n + 1
                                             /\ \A e \in S : e[n+1] = e1[n+1]
                                             THEN LongestCommonPrefixLenRec(S, n+1, e1)
                                             ELSE n

LongestCommonPrefixLenSet(S) == LongestCommonPrefixLenRec(S, 0, SetPick(S))

LongestCommonPrefix(S) == LET n == LongestCommonPrefixLenSet(S)
                          IN IF n = 0 THEN <<>>
                             ELSE [i \in 1..LongestCommonPrefixLenSet(S) |-> SetPick(S)[i]]



=============================================================================
\* Modification History
\* Last modified Sun Jul 08 20:15:43 EDT 2018 by ailidani
\* Created Mon Jul 17 17:37:04 PDT 2017 by ailidani
