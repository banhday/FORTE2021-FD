----------------------------- MODULE sa_cntr_d2 -----------------------------
(* The eventually perfect failure detectors in Figure 10 [1] under partially 
   synchronous constraints of the DLS computational model [2] is encoded as 
   natural counters and in TLA+.  
  
   [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for 
   reliable distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.
   
   [2] Dwork, Cynthia, Nancy Lynch, and Larry Stockmeyer. "Consensus in the presence 
   of partial synchrony." Journal of the ACM (JACM) 35.2 (1988): 288-323.                                                                 
  
   Thanh-Hai Tran, Igor Konnov, Josef Widder, 2020
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE. 
 *)


(*   
  - In this specification, Delta is fixed to 2.
  - Instead of two isomorphic processes under renaming, we here assume that one 
    process is a sender and another is a receiver. Prefix S_ is for the sender, 
    and prefix R_ is for the receiver.
  - There exists only one communication channel from the sender to the receiver 
    named buf. 
  - This communication channel buf is encoded as a natural-numbered counter
    in this specification. The user can also consider buf as a bit-vector with
    Delta+1 bits. Moreover, we read and write the bit-vector buf from right 
    to left. The right-most bit is indexed with 0.
  - For every k < Delta, the k-th bit of buf implies that there exists a 
    message which is k time-unit old in the channel. For example, the bit-vector 
    001 implies there exists a message that is 0 time-unit old in the channel.
    A fresh message in the channel buf is 0 time-unit old.  
  - The Delta-th bit has a special meaning. Here we have an abstraction on 
    in-transit messages that are older than Delta time-unit old. Instead of 
    keeping track of each old message, we only set the Delta-th bit on if
    those messages exist. For example, assume that Delta = 2, and there are
    only two in-transit messages such that one is 1 time-unit old and another
    is 2 time-units old. The buf in this case is 011 (in binary).            
  - Every global transition has four sub-rounds: Schedule, Send, Receive, 
    and Local Computation. Transitions for these sub-rounds are call internal
    ones.
  - Only the environment is active in the sub-round Schedule.
  - While the sender may be active in three sub-rounds Send, Receive, and Local
    Computation, it does nothing in two sub-rounds: Receive and Local Computation. 
  - The receiver may be active in three sub-rounds: Send, Receive and Local 
    Computation. If the receiver is active in the sub-round Send, it only 
    updates its waiting time.      
  - More details about four sub-rounds are provided later. We will refine them
    into a sequence of actions.
  *)              
EXTENDS Naturals, TLC

CONSTANTS Phi                    \* The bound on relaive process speed
ASSUME 1 <= Phi

Delta == 2
TODefault == 6*Phi + Delta       \* Default value of timeout


ASSUME TODefault >= 6*Phi + Delta

(* 
  The set Action contains processes' actions:     
    - SSched: decide whether the sender is active in the current global transition
    - RSched: decide whether the receiver is active in the
      current global transition
    - IncMsgAge: increases the age of every in-transit message
    - SSnd: if the sender is active in the phase Send, it sends a new message.
    - RNoSend: if the receiver is active in the phase Send, it increases its
      waiting time for the sender.
    - RRcv: if the receiver is active in the phase Receive, it executes an
      instruction Receive, and updates its variables.
    - RComp: if the receiver is active in the phase Local Computation, it updates
      its suspecion on the sender based on messages that have been delivered recently.
  In this TLA+ specification, these actions are encoded as (atomic) transitions.      
  A transition for the sub-round Schedule contains a sequence of actions: 
      SSched --> RSched --> IncMsgAge.
  A transition for the sub-round Send contains a sequence of small transitions:
      SSnd --> RNoSnd.         
  Remind that the active sender does nothing in these phases Receive and Local 
  Computation. Hence, a transition for the sub-round Receive contains only one  
  action RRcv. A transition for the sub-round Local Computation contains only  
  one action RComp.
  *)
Action == { "SSched", "RSched", "IncMsgAge", "SSnd", "RNoSnd", "RRcv", "RComp" }
   

VARIABLES suspected,      \* whether the receiver suspects the sender
          waitingTime,    \* how long the receiver has not heard from the sender                          
          timeout,        \* how long the receiver can wait for the sender                                                     
          sPC,            \* pc of the sender
          rPC,            \* pc of the receiver
          buf,             \* the communication channel that is encoded with two bits 
                          \* in this specification                                                    
          sTimer,         \* how long the sender has not taken a step
          rTimer,         \* how long the sender has not taken a step    
          ePC             \* pc of the environment
 
vars == << buf, sTimer, rTimer, ePC, 
           suspected, waitingTime, timeout, sPC, rPC >>          
              
\* The initialization              
Schedule_Init ==   
  /\ sTimer = 0
  /\ rTimer = 0
  /\ ePC = "SSched"  
         
Proc_Init ==
  /\ sPC = "SSnd" 
  /\ rPC = "RComp"
  /\ buf = 0       
  /\ suspected = FALSE
  /\ waitingTime = 0
  /\ timeout = TODefault   
  
Init == Proc_Init /\  Schedule_Init       

(* 
  - The sender non-deterministically becomes active.
  - If the sender is inactive, the constraint sTimer < Phi - 1 must hold.
  - After the environment decides to activate the sender, it changes the pc of the
    sender.
  *)
SSched ==  
  /\ ePC = "SSched"
  /\ ePC' = "RSched"  
  /\ \/ /\ sTimer >= 2           /* ensures that the sender went through sub-rounds Receive and Local Computation
        /\ sTimer' = 0          
        /\ UNCHANGED sPC                                                                         
     \/ /\ sTimer < 3 * Phi - 1
        /\ sTimer' =  sTimer + 1
        /\ UNCHANGED sPC                                       
  /\ UNCHANGED << buf, rTimer, rPC, suspected, waitingTime, timeout >>                                   
     

(* 
  - The receiver non-deterministically becomes active.
  - If the receiver is inactive, the constraint rTimer < Phi - 1 must hold.
  - After the environment decides to activate the receiver, it changes the pc of the
    receiver.
  *)                                     
RSched ==  
  /\ ePC = "RSched"
  /\ ePC' = "IncMsgAge"  
  /\ \/ /\ rTimer' = 0      
        /\ \/ /\ rPC = "RNoSnd"                       
              /\ rPC' = "RRcv"                      
           \/ /\ rPC = "RRcv"                         
              /\ rPC' = "RComp"                      
           \/ /\ rPC = "RComp"                      
              /\ rPC' = "RNoSnd"                      
     \/ /\ rTimer < Phi - 1
        /\ rTimer' = rTimer + 1                
        /\ UNCHANGED rPC                              
  /\ UNCHANGED << buf, sTimer, sPC, suspected, waitingTime, timeout >> 
          

(* 
  - We simulate the ageing process of in-transit messages by multiplying buf by 2.
    Image that buf = 010 (in binary). We know that there exists a message that was
    1 time-unit old. After ageing, this message is 2 time-unit old, and buf' should 
    be 100. By multiplying buf by 2, we actually move each bit in buf left. This
    action simulates the increase of messages' age by 1.
  - Another example, let buf = 011 (in binary). After executing IncMsgAge, then 
    we have that buf' = 110.
       
  - Observation: Let Delta = 2. Assume that there exist two in-transit messages m1 and 
    m2 such that m1 is 1 time-unit old, and m2 is 2 time-unit old. Hence, we have that 
    buf = 110 (again in binary). We know buf * 2 = 1100. The problem is that we 
    now need an extra bit to represent buf'. Our target is to use only 3 bits to  
    represent buf'. In order to do that, we apply optimizations and abstractions. 
  - Continue with the above example buf = 110 and buf' = 1100. We know that if the 
    receiver executes an instruction Receiver later, it will receive messages m1 and m2 
    together, and believe that the sender is still alive. A good observation is that
    the decision of the receiver in the phase Receive depends on only whether it has 
    received a message from the sender, not exactly what messages have just delivered.
    For example, consider two following cases 
      a) buf = 1100 when the receiver executes an instruction Receiver.
      b) buf = 100 when the receiver executes an instruction Receiver.
    If Delta = 2, the receivers in both cases a) and b) make the same decision. Both 
    receivers believe that the sender is still alive. 
  - Our first optimization is to throw away bits indexed from Delta + 1 if the Delta-th 
    bit is 0. 
  - We go further. If there exists a bit whose index is at least Delta + 1 is 1 but the 
    Delta-th bit is 0, we first throw away bits indexed from Delta + 1, and set the 
    Delta-th bit is 1. For example, assume that Delta = 2the actual value of buf is 
    1000 (in binary). Instead of 1000, now we set buf = 100. If the receiver executes
    an instruction Receiver later, it has the same decision in both cases (buf = 1000
    and buf = 100).
    
  - The condition buf < 2^Delta checks whether the Delta-th bit in buf is 0. In this
    case, we do not need to throw away any bits after multiplying buf by 2.
  - The condition buf >= 2^Delta + 2^(Delta - 1) checks whether both of the Delta-th 
    and (Delta-1)-th bits are 1? If so, after multiplying buf by 2, we need to only 
    throw away the Delta-th bit. The subtraction of buf * 2 by 2^(Delta + 1) in this
    case implies that we reset the (Delta+1)-th bit is 0. 
  - The last is for the case that the Delta-th bit is 1 but the (Delta-1)-th bit is 1. 
    Hence, the binary representation of (buf * 2) has (i) the (Delta+1)-th bit is 1, 
    and (ii) the Delta-th bit is 0. Hence, in addition to throw away the (Delta+1)-th bit,
    we need to set the Delta-th bit of buf' to 1. We do that by adding 2^Delta to
    (buf * 2 - 2^(Delta + 1)).          
  *)
IncMsgAge ==            
  /\ ePC = "IncMsgAge"
  /\ ePC' = "SSnd"    
  /\ IF buf < 2^Delta
     THEN buf' = (buf * 2) 
     ELSE IF buf >= 2^Delta + 2^(Delta - 1)
          THEN buf' = ((buf - 2^Delta) * 2) 
          ELSE buf' = ((buf - 2^Delta) * 2) + 2^Delta     
  /\ UNCHANGED << sTimer, rTimer,  
           suspected, waitingTime, timeout, sPC, rPC >>                                      
  
  
(* 
  - After IncreaseMsgAge, the 0-th bit is always 0 if Delta > 0. To capture the appearance 
    of a fresh message in buf', we simply add 1 to buf. If the sender is inactive
    in the sub-round Send, we keep buf unchanged.
  *)   
SSnd == 
  /\ ePC = "SSnd"
  /\ ePC' = "RNoSnd"  
  /\ IF (sTimer = 0 /\ sPC = "SSnd")  \* whether the sender is active in the sub-round Send
     THEN buf' = buf + 1              \* add a new message to the communication channel        
     ELSE UNCHANGED buf
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC, suspected, waitingTime, timeout >>
  
(* 
  - If the receiver is active in the sub-round Send, it does not receive any message from
    the sender. Hence, it increases its waiting time for the sender.
  - We have here an optimization. If the waiting time reaches the timeout, then we stop
    increasing the waiting time. Remind that the waiting time is used only in the sub-round
    Local Computation when the receiver thinks that it should suspect the sender. To do that,
    the receiver checks the condition waitingTime >= timeOut. Hence, we do not need to 
    increase the waiting time whenever it reaches the time out. This optimization helps us
    reduce the state space.
  *)     
RNoSnd ==  
  /\ ePC = "RNoSnd"
  /\ ePC' = "RRcv"  
  /\ IF (rTimer = 0 /\ rPC = "RNoSnd")  \* is the receiver active in the sub-round Send?
     THEN /\ IF waitingTime < timeout
             THEN waitingTime' = waitingTime + 1
             ELSE UNCHANGED waitingTime
          /\ UNCHANGED << buf, sTimer, rTimer, sPC, rPC,
                        suspected, timeout >>
     ELSE UNCHANGED << buf, sTimer, rTimer, 
           suspected, waitingTime, timeout, sPC, rPC >>                                                        

(* 
  - The following is to represent the delivery of in-transit messages. Here we enumerate
    all possible cases. The name MsgDeliverK implies that the current value of buf is K.
  - Recall that in this specification, we fix Delta = 2.    
  - MsgDeliver1: only a fresh message in the channel. If this message is delivered, then the 
    channel is empty. Hence, we set buf' = 0. Next, the waiting time is reset to 0.
    Moreover, if the receiver suspected the sender and new messages have been delivered, 
    then the receiver trusts the sender again, and increases its waiting time for the sender.       
  *) 
MsgDeliver1 ==   
  /\ buf = 1        \* buf  = 001 in binary
  /\ buf' = 0       \* buf' = 000 in binary                  
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
  

MsgDeliver2 ==   
  /\ buf = 2        \* buf  = 010 in binary
  /\ buf' = 0       \* buf' = 000 in binary                  
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>  


MsgDeliver3 ==   
  /\ buf = 3         \* buf  = 011 in binary
  /\ \/ buf' = 0     \* buf' = 000  \* Deliver both m0 and m1
     \/ buf' = 1     \* buf' = 001  \* Deliver only m1
     \/ buf' = 2     \* buf' = 010  \* Deliver only m0                  
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>   
  

MsgDeliver4 ==   
  /\ buf = 4        \* buf  = 100 in binary
  /\ buf' = 0       \* buf' = 000 in binary
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>   
  

MsgDeliver5 ==   
  /\ buf = 5        \* buf  = 101 in binary
  /\ \/ buf' = 0    \* buf  = 000 in binary
     \/ buf' = 1    \* buf  = 001 in binary                        
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
  

MsgDeliver6 ==   
  /\ buf = 6        \* buf  = 110 in binary
  /\ \/ buf' = 0    \* buf' = 000 in binary
     \/ buf' = 2    \* buf' = 010 in binary                        
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>  
  

MsgDeliver7 ==   
  /\ buf = 7        \* buf  = 111 in binary
  /\ \/ buf' = 0    \* buf' = 000 in binary
     \/ buf' = 1    \* buf' = 001 in binary
     \/ buf' = 2    \* buf' = 010 in binary
     \/ buf' = 3    \* buf' = 011 in binary                        
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >> 


(*
  - No messages will be delivered. This action requires that every in-transit messages is young. 
    Since the Delta-th bit is 0 and buf has only Delta + 1 bits, the maximum value of buf
    in this case is where every bit indexed from 0 to Delta-1 is 1. Remind that  
        2^0 + 2^1 + ... + 2^(Delta - 1) = 2^Delta - 1 
    Hence, in order to check whether the Delta-th bit is 0, we can use the following condition 
        buf < 2^Delta.
  *)  
NoMsgDeliver ==  
  /\ buf < 2^Delta
  /\ UNCHANGED buf
  /\ IF waitingTime < timeout
     THEN waitingTime' = waitingTime + 1
     ELSE UNCHANGED waitingTime                 
  /\ UNCHANGED << suspected, timeout, sTimer, rTimer, sPC, rPC >>       
  
\* Receive new messages. 
RRcv ==
  /\ ePC = "RRcv"
  /\ ePC' = "RComp"
  /\ IF (rTimer = 0 /\ rPC = "RRcv")  \* is the receiver active in the sub-round Receive?
     THEN \/ NoMsgDeliver 
          \/ MsgDeliver1 
          \/ MsgDeliver2
          \/ MsgDeliver3
          \/ MsgDeliver4
          \/ MsgDeliver5
          \/ MsgDeliver6
          \/ MsgDeliver7          
     ELSE UNCHANGED << buf, sTimer, rTimer,  
           suspected, waitingTime, timeout, sPC, rPC >>
     
(* 
  - The receiver updates its suspicion based on its waiting time and time out. There are 
    four cases:
      a) The waiting time has not reached the time out. The active receiver still trusts 
         the sender. The receiver increases the waiting time by 1.
      b) The waiting time has reached the time out, but the active receiver did not suspect 
         the sender. Now, the receiver suspects the sender.
      c) The waiting time reached the time out, and the receiver already suspected the sender. 
         Then all variables are unchanged.  
      d) The receiver is not active.
 *)             
RComp ==                         
  /\ ePC = "RComp"
  /\ ePC' = "SSched"
  /\ IF rTimer = 0 /\ rPC = "RComp" 
     THEN /\ IF waitingTime < timeout
             THEN /\ waitingTime' = waitingTime + 1   \* increase the waiting time
                  /\ UNCHANGED suspected              \* still trust the sender  
             ELSE /\ IF ~suspected  
                     THEN suspected' = TRUE
                     ELSE UNCHANGED suspected
                  /\ UNCHANGED waitingTime
          /\ UNCHANGED << buf, sTimer, rTimer, sPC, rPC, timeout>>                      
     ELSE UNCHANGED << buf, sTimer, rTimer, sPC, rPC,
                waitingTime, timeout, suspected >>   
                
\* Transitions                                                                                          
Next == 
  \/ SSched
  \/ RSched
  \/ IncMsgAge
  \/ SSnd
  \/ RNoSnd  
  \/ RRcv  
  \/ RComp           
  
Spec == 
  /\ Init 
  /\ [][Next]_vars 
  /\ WF_vars( Next )
               
\* Type information 
TypeOK ==    
  /\ buf \in 0..(2^(Delta + 1) - 1)
  /\ sTimer \in 0..(3*Phi - 1)
  /\ rTimer \in 0..(Phi - 1)
  /\ ePC \in {"SSched", "RSched", "IncMsgAge", "SSnd", 
                  "RNoSnd", "RRcv", "RComp"}  
  /\ suspected \in BOOLEAN  
  /\ timeout = 6 * Phi + Delta
  /\ waitingTime \in 0..(timeout - 1) 
  /\ sPC \in {"SSnd"} 
  /\ rPC \in {"RNoSnd", "RRcv", "RComp"}

\* Since there are no crashes, the safety property Strong Accuracy 
\* can be rewritten as the following    
StrongAccuracy == ~suspected

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 11:21:04 CET 2021 by tran
\* Created Wed Jan 20 09:38:24 CET 2021 by tran
