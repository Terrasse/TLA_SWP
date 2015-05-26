------------------------------ MODULE SlidingWindowProtocol ------------------------------
EXTENDS Integers, Naturals
      
CONSTANT l, n

VARIABLES IN1,
          OUT,
          i,
          ack,
          got,
          b
          
vars == <<IN1,OUT, i, ack, got, b>>

-----------------------------------------------------------------
INITIALISATION == /\ OUT = {}
                  /\ i = 0
                  /\ ack = {}
                  /\ got = {}
                  /\ b = {}
                  
-----------------------------------------------------------------
SEND(j) == /\ j \in i..i+1
           /\ j \notin got
           /\ j - i > 0 
           /\ j - i < l
           /\ b(j-i) = IN1(j)
           /\ UNCHANGED <<i, ack, got, OUT>>
           
-----------------------------------------------------------------
RECEIVE(j) == /\ j \in i..i+1
              /\ j - i \in dom(b)
              /\ ack = ack \union {j}
              /\ OUT(j) = b(j-i)
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
              \*
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
              /\ j-i \in dom(b)
              /\ b' = {j - i} \* ca veut dire quoi?
              /\ UNCHANGED <<i,OUT, got, ack>>  
              
-----------------------------------------------------------------
LOOSINGACK(k) == /\ k \in ack
              /\ ack' = ack \ k
              /\ UNCHANGED <<i,OUT, got, b>> 

                          
inv1 == OUT \subseteq IN1
\* inv2 == que veut dire la fleche ?
inv3 == i > 0 /\ i < n + 1
inv4 == ack \union got \subseteq (i .. i+l) \intersect 0 .. n
inv5 == ack \subseteq dom(OUT)
inv6 == OUT \in Naturals \* ??
inv7 == i \in 0..n+1
inv8 == 0..i-1 \subseteq dom(OUT) /\ dom(OUT) \subseteq 0..n
inv9 == ack \subseteq Naturals
inv10 == got \subseteq Naturals
inv11 == got \subseteq dom(OUT)
inv12 == ack \subseteq dom(OUT)
\* inv13 même question que inv2


                     
      
=================================================================              