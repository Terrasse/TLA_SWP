------------------------------ MODULE SlidingWindowProtocol ------------------------------
EXTENDS Naturals, Sequences
      
CONSTANT l, n, N

VARIABLES OUT,
          IN1,
          i,
          state,
          tmp_j,
          ack,
          got,
          b \* fenetre deux cursor -- buffer

DOM_IN == 0..n
DOM_OUT == 0..n
DOM_B == 0..l-1
D == 0..N

-----------------------------------------------------------------
INITIALISATION == /\ OUT = [s \in DOM_OUT |-> {}]
                  /\ i = 0
                  /\ ack = {}
                  /\ got = {}
                  /\ b = [s \in DOM_B |-> 9999999]
                  /\ tmp_j = 0
                  /\ state = "INIT"
                  /\ IN1 = [s \in DOM_IN |-> 
                            IF s = 0 THEN 10 ELSE 
                            IF s = 1 THEN 11 ELSE 
                            IF s = 2 THEN 12 ELSE
                            IF s = 3 THEN 13 ELSE
                            IF s = 4 THEN 14 ELSE s]
              
-----------------------------------------------------------------
SEND(j) == 
           /\ j \in i..i+l-1 
           /\ j \leq n-1
           /\ <<j>> \notin got
           /\ state' = "SEND"
           /\ tmp_j' = j
           /\ b'= [b EXCEPT ![j-i] = IN1[j]]
           /\ UNCHANGED <<i,ack, IN1, OUT,got,IN1>>     
        
-----------------------------------------------------------------
RECEIVE(j) == /\ j \in i..i+l               \*grd2
              /\ (j-i) \in DOM_B               \*grd3 
              /\ ack' = ack \union {<<j>>}
              /\ b[j-i] \in D
              /\ OUT'=[OUT EXCEPT![j]=b[j-i]]
              /\ state' = "RECEIVE"
              /\ tmp_j' = j
              /\ UNCHANGED <<i, got, b, IN1>>

-----------------------------------------------------------------
RECEIVEACK(k) == 
              /\ <<k>> \in ack
              /\ got' = got \union {<<k>>}
              /\ ack' = ack \ {<<k>>}
              /\ state' = "RECEIVEACK"
              /\ tmp_j' = k
              /\ UNCHANGED <<i,OUT, b, IN1>>          
         
 
-----------------------------------------------------------------
SLIDING(c) == /\ got # {}
              /\ <<i>> \in got
              /\ i + l < n
              \*/\ c \in 1..l-1 
              \*/\ b[c] \in D
              /\ i' = i + 1
              /\ got' = got \ {<<i>>}
              /\ ack' = ack \ {<<i>>}
              /\ b'= [[[b EXCEPT![0]=b[1]] EXCEPT![1]=b[2]] EXCEPT![2]=9999999]
              /\ state' = "SLIDING"
              /\ UNCHANGED <<OUT,IN1,tmp_j>>      
         
-----------------------------------------------------------------
EMPTYWINDOW(c) == 
              /\ got # {}
              /\ <<i>> \in got
              /\ i + l \geq n
              /\ i \leq n
              /\ c \in 1..l-1 
              /\ b[c] \in D
              /\ i' = i + 1
              /\ got' = got \ {<<i>>}
              /\ ack' = ack \ {<<i>>}
              /\ state' = "EMPTYWINDOW"
              /\ b'= [[[b EXCEPT![c-1]=b[c]] EXCEPT![c]=b[c+1]] EXCEPT![c+1]=9999999]
              /\ UNCHANGED <<tmp_j,OUT,IN1>>    

-----------------------------------------------------------------
COMPLETION == /\ i = n+1
              /\ got = {}
              /\ state' = "END"
              /\ UNCHANGED <<i,OUT, b, ack,got,IN1,tmp_j>>  

-----------------------------------------------------------------
LOOSINGCHAN(j) == 
              /\ j \in i..i+l
              /\ <<j>> \notin got
              /\ b[j - i] # {}
              /\ b'= [b EXCEPT ![j-i] = {}] \* on enleve la valeur de b[j-i]
              /\ state' = "LOOSINGCHAN"
              /\ tmp_j' = j
              /\ UNCHANGED <<b,i,OUT, got, ack,IN1>>  
              
-----------------------------------------------------------------
LOOSINGACK(k) == 
              /\ <<k>> \in ack
              /\ ack' = ack \ {<<k>>}
              /\ state' = "LOOSINGACK"
              /\ tmp_j' = k
              /\ UNCHANGED <<i,OUT, got, b,IN1>> 
-----------------------------------------------------------------
Next == \E j \in DOM_IN: SEND(j) \/ RECEIVE(j) \/ RECEIVEACK(j) \/ SLIDING(j) \/ EMPTYWINDOW(j) \/ COMPLETION
-----------------------------------------------------------------
Init == INITIALISATION
                          
inv1 == OUT \subseteq IN1
\* inv2 == que veut dire la fleche ?
inv3 == i > 0 /\ i < n + 1
inv4 == ack \union got \subseteq (i .. i+l) \intersect 0 .. n
inv5 == ack \subseteq DOM_OUT
inv6 == OUT \in D \* ??
inv7 == i \in 0..n+1
inv8 == 0..i-1 \subseteq DOM_OUT /\ DOM_OUT \subseteq 0..n
inv9 == ack \subseteq D 
inv10 == got \subseteq D 
inv11 == got \subseteq DOM_OUT
inv12 == ack \subseteq DOM_OUT
\* inv13 même question que inv2

reachend == i < 10


                     
      
=================================================================              