-------------------------- MODULE sa_iinv_cntr_d2 --------------------------

EXTENDS Naturals, TLC

CONSTANTS Phi             \* The bound on relaive process speed
ASSUME 1 <= Phi

Delta == 2
TODefault == 6*Phi + Delta      \* Default value of timeout


ASSUME TODefault >= 6*Phi + Delta

Action == { "SSched", "RSched", "IncMsgAge", "SSnd", "RNoSnd", "RRcv", "RComp" }
   

VARIABLES suspected,      \* whether the receiver suspects the sender
          waitingTime,    \* how long the receiver has not heard from the sender                          
          timeout,        \* how long the receiver can wait for the sender                                                     
          sPC,            \* pc of the sender
          rPC,            \* pc of the receiver
          buf,         \* the communication channel that is encoded with two bits 
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


SSched ==  
  /\ ePC = "SSched"
  /\ ePC' = "RSched"  
  /\ \/ /\ sTimer >= 2
        /\ sTimer' = 0          
        /\ UNCHANGED sPC                                                                         
     \/ /\ sTimer < 3 * Phi - 1
        /\ sTimer' =  sTimer + 1
        /\ UNCHANGED sPC                                       
  /\ UNCHANGED << buf, rTimer, rPC, suspected, waitingTime, timeout >>                                   
     
                                  
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
  
  
SSnd == 
  /\ ePC = "SSnd"
  /\ ePC' = "RNoSnd"  
  /\ IF (sTimer = 0 /\ sPC = "SSnd")  \* whether the sender is active in the sub-round Send
     THEN buf' = buf + 1              \* add a new message to the communication channel        
     ELSE UNCHANGED buf
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC, suspected, waitingTime, timeout >>
  
  
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


NoMsgDeliver ==  
  /\ buf < 2^Delta
  /\ UNCHANGED buf
  /\ IF waitingTime < timeout
     THEN waitingTime' = waitingTime + 1
     ELSE UNCHANGED waitingTime                 
  /\ UNCHANGED << suspected, timeout, sTimer, rTimer, sPC, rPC >>       
  
  
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
                
                                             
Next == 
  \/ SSched
  \/ RSched
  \/ IncMsgAge
  \/ SSnd
  \/ RNoSnd  
  \/ RRcv  
  \/ RComp           
  
\* We check two liveness properties Strong Completeness and Eventually Strong Accuracy in Spec   
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

    
StrongAccuracy == ~suspected

Constraint1 ==
  /\ ((buf = 0 /\ waitingTime > 0 /\ waitingTime < 3*Phi)
        => sTimer >= waitingTime)
           
  
Constraint2 == 
  /\ waitingTime = 3*Phi => buf > 0
  /\ waitingTime >= 3*Phi + 1 => buf >= 2^1 
  /\ waitingTime >= 3*Phi + Delta => buf >= 2^Delta 
  
Constraint3 ==
  /\ ((waitingTime >= 5*Phi + Delta) => 
          ( /\ rTimer >= waitingTime - 5*Phi - Delta
            /\ rPC = "RNoSnd"))
  /\ (( /\ waitingTime >= 4*Phi + Delta
        /\ waitingTime <  5*Phi + Delta ) =>
          ( /\ rPC = "RNoSnd" \/ rPC = "RComp"
            /\ rPC = "RComp" => rTimer >= waitingTime - 4*Phi - Delta) )
  /\ (( /\ waitingTime >= 3*Phi + Delta
        /\ waitingTime <  4*Phi + Delta ) =>
          ( /\ rPC = "RNoSnd" \/ rPC = "RComp" \/ rPC = "RRcv"             
            /\ rPC = "RRcv" => rTimer > waitingTime - 3*Phi - Delta))               

  
ConstraintsInIndInv_BigStep ==
  /\ TypeOK
  /\ StrongAccuracy
  /\ Constraint1  
  /\ Constraint2
  /\ Constraint3   


IndInv_BigStep ==
  \/ ePC # "SSched"
  \/ ConstraintsInIndInv_BigStep
  
  
Init_IndInv_BigStep ==
  /\ ePC = "SSched"
  /\ ConstraintsInIndInv_BigStep  


=============================================================================
\* Modification History
\* Last modified Thu Jan 21 12:18:48 CET 2021 by tran
\* Created Wed Jan 20 10:06:11 CET 2021 by tran
