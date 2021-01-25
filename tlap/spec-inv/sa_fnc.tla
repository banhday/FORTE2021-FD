------------------------------- MODULE sa_fnc -------------------------------

EXTENDS Naturals, TLC

CONSTANTS Phi, Delta             \* The bound on relaive process speed
ASSUME 1 <= Phi

ASSUME Delta >= 0

TODefault == 6*Phi + Delta       \* Default value of timeout
ASSUME TODefault >= 6*Phi + Delta

Action == { "SSched", "RSched", "IncMsgAge", "SSnd", "RNoSnd", "RRcv", "RComp" }
MsgAge == 0..Delta
   

VARIABLES suspected,      \* whether the receiver suspects the sender
          waitingTime,    \* how long the receiver has not heard from the sender                          
          timeout,        \* how long the receiver can wait for the sender                                                     
          sPC,            \* pc of the sender
          rPC,            \* pc of the receiver
          existsMsgOfAge,         \* the communication channel that is encoded with two bits 
                          \* in this specification                                                    
          sTimer,         \* how long the sender has not taken a step
          rTimer,         \* how long the sender has not taken a step    
          ePC             \* pc of the environment
 
vars == << existsMsgOfAge, sTimer, rTimer, ePC, 
           suspected, waitingTime, timeout, sPC, rPC >>          
              
\* The initialization              
Schedule_Init ==   
  /\ sTimer = 0
  /\ rTimer = 0
  /\ ePC = "SSched"  
         
Proc_Init ==
  /\ sPC = "SSnd" 
  /\ rPC = "RComp"
  /\ existsMsgOfAge = [i \in MsgAge |-> FALSE ]       
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
  /\ UNCHANGED << existsMsgOfAge, rTimer, rPC, suspected, waitingTime, timeout >>                                   
     
                                  
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
  /\ UNCHANGED << existsMsgOfAge, sTimer, sPC, suspected, waitingTime, timeout >>     


IncMsgAge ==            
  /\ ePC = "IncMsgAge"
  /\ ePC' = "SSnd"    
  /\ IF Delta = 0
     THEN UNCHANGED existsMsgOfAge
     ELSE /\ existsMsgOfAge' \in [MsgAge -> BOOLEAN ]
          /\ existsMsgOfAge'[Delta] = (existsMsgOfAge[Delta] \/ existsMsgOfAge[Delta - 1])
          /\ ~existsMsgOfAge'[0]
          /\ \A k \in 0..(Delta - 2) : existsMsgOfAge'[k + 1] = existsMsgOfAge[k]               
  /\ UNCHANGED << sTimer, rTimer,  
           suspected, waitingTime, timeout, sPC, rPC >>                                  
   

SSnd ==  
  /\ ePC = "SSnd"
  /\ ePC' = "RNoSnd"  
  /\ IF (sTimer = 0 /\ sPC = "SSnd")  \* whether the sender is active in the sub-round Send
     THEN existsMsgOfAge' = [ existsMsgOfAge EXCEPT ![0] = TRUE ]        
     ELSE UNCHANGED existsMsgOfAge
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC, suspected, waitingTime, timeout >>
  
  
RNoSnd ==  
  /\ ePC = "RNoSnd"
  /\ ePC' = "RRcv"  
  /\ IF (rTimer = 0 /\ rPC = "RNoSnd")  \* is the receiver active in the sub-round Send?
     THEN /\ IF waitingTime < timeout
             THEN waitingTime' = waitingTime + 1
             ELSE UNCHANGED waitingTime
          /\ UNCHANGED << existsMsgOfAge, sTimer, rTimer, sPC, rPC,
                        suspected, timeout >>
     ELSE UNCHANGED << existsMsgOfAge, sTimer, rTimer, 
           suspected, waitingTime, timeout, sPC, rPC >>
           
           
MsgDeliver ==
  /\ \E k \in MsgAge : existsMsgOfAge[k]
  /\ existsMsgOfAge' \in [MsgAge -> BOOLEAN ]
  /\ ~existsMsgOfAge'[Delta]
  /\ \E k \in MsgAge : existsMsgOfAge'[k] # existsMsgOfAge[k]
  /\ \A k \in MsgAge : existsMsgOfAge'[k] => existsMsgOfAge[k]          
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
                                                                     

NoMsgDeliver ==  
  /\ ~existsMsgOfAge[Delta]
  /\ UNCHANGED existsMsgOfAge
  /\ IF waitingTime < timeout
     THEN waitingTime' = waitingTime + 1
     ELSE UNCHANGED waitingTime                 
  /\ UNCHANGED << suspected, timeout, sTimer, rTimer, sPC, rPC >>       
  

RRcv ==
  /\ ePC = "RRcv"
  /\ ePC' = "RComp"
  /\ IF (rTimer = 0 /\ rPC = "RRcv")  \* is the receiver active in the sub-round Receive?
     THEN \/ MsgDeliver
          \/ NoMsgDeliver
     ELSE UNCHANGED << existsMsgOfAge, sTimer, rTimer,  
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
          /\ UNCHANGED << existsMsgOfAge, sTimer, rTimer, sPC, rPC, timeout>>                      
     ELSE UNCHANGED << existsMsgOfAge, sTimer, rTimer, sPC, rPC,
                waitingTime, timeout, suspected >>   
                
                                             
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
               
 
TypeOK ==    
  /\ existsMsgOfAge \in [MsgAge -> BOOLEAN]
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
  
=============================================================================
\* Modification History
\* Last modified Thu Jan 21 12:38:12 CET 2021 by tran
\* Created Tue Jan 19 13:02:31 CET 2021 by tran
