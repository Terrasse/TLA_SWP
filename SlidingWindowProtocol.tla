------------------------------ MODULE SlidingWindowProtocol ------------------------------
EXTENDS Integers, Naturals
      
CONSTANT l, n, N, IN1

VARIABLES OUT,
          i,
          ack,
          got,
          b \* fenetre deux cursor -- buffer

DOM_IN == 0..n \* création tableau de 0 à n -- i et j pas depends represente les indices du tableau in
DOM_OUT == 0..n
DOM_B == 0..n  
MyNat == 0..N
   
vars == <<IN1,OUT, i, ack, got, b>>

-----------------------------------------------------------------
INITIALISATION == /\ OUT = {}
                  /\ i = 0
                  /\ ack = {}
                  /\ got = {}
                  /\ b = {}
                  
-----------------------------------------------------------------
SEND(j) == /\ j \in i..i+l
           \*/\ j - i > 0 
           \*/\ j - i < l
           /\ j \leq n 
           /\ j \notin got
           /\ j-i \in 0..l      
           /\ b'=[b EXCEPT! [b-j]=IN1[j]] \* /\ b[j-i]' = IN1[j]
           /\ UNCHANGED <<i, ack, got, OUT>>
           
-----------------------------------------------------------------
RECEIVE(j) == /\ j \in i..i+l
              /\ j - i \in DOM_B
              /\ ack' = ack \union {j}
              /\ OUT'=[OUT EXCEPT![j]=b[j-i]]  \* /\ OUT(j)' = b(j-i) \* pour modifir la valeur 
              /\ UNCHANGED <<i, ack, got, b>>

-----------------------------------------------------------------
RECEIVEACK(k) == /\ k \in ack
              /\ got' = got \union {k}
              /\ ack' = ack \ {k}
              /\ UNCHANGED <<i,OUT, b>>          
         
 
-----------------------------------------------------------------
SLIDING(c) == /\ got # {}
              /\ i \in got
              /\ i + l < n
              /\ i' = i + 1
              /\ got' = got \ {i}
              /\ ack' = ack \ {i}
              /\ b' = c
              /\ UNCHANGED <<OUT>>      
         
-----------------------------------------------------------------
EMPTYWINDOW(c) == /\ got # {}
              /\ i \in got
              /\ i + l >= n
              /\ i <= n
              \*
              /\ i' = i + 1  
              /\ got' = got \ {i}
              /\ ack' = ack \ {i}
              /\ b' = c       
              /\ UNCHANGED <<OUT>>  

-----------------------------------------------------------------
COMPLETION == /\ i = n+1
              /\ got' = {}
              /\ UNCHANGED <<i,OUT, b, ack>>  
              \* skip

-----------------------------------------------------------------
LOOSINGCHAN(j) == /\ j > i
              /\ j < i + 1
              /\ j \notin got
              /\ j-i \in DOM_IN
              /\ b' = {j - i} \* ca veut dire quoi?
              /\ UNCHANGED <<i,OUT, got, ack>>  
              
-----------------------------------------------------------------
LOOSINGACK(k) == /\ k \in ack
              /\ ack' = ack \ k
              /\ UNCHANGED <<i,OUT, got, b>> 
-----------------------------------------------------------------
Next == \/ \E j \in DOM_IN: SEND(j)
        \/ \E j \in DOM_IN: RECEIVE(j)
        \/ \E j \in DOM_IN: RECEIVEACK(k)
-----------------------------------------------------------------
                          
inv1 == OUT \subseteq IN1
\* inv2 == que veut dire la fleche ?
inv3 == i > 0 /\ i < n + 1
inv4 == ack \union got \subseteq (i .. i+l) \intersect 0 .. n
inv5 == ack \subseteq DOM_OUT
inv6 == OUT \in MyNat \* ??
inv7 == i \in 0..n+1
inv8 == 0..i-1 \subseteq DOM_OUT /\ DOM_OUT \subseteq 0..n
inv9 == ack \subseteq MyNat
inv10 == got \subseteq MyNat
inv11 == got \subseteq DOM_OUT
inv12 == ack \subseteq DOM_OUT
\* inv13 même question que inv2


                     
      
=================================================================              