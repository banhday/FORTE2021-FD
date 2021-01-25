----------------------------- MODULE sa_cntr_d4_wrong -----------------------------

EXTENDS Naturals, TLC

CONSTANTS Phi             \* The bound on relaive process speed
ASSUME 1 <= Phi

Delta == 4
TODefault == 1 + Delta      \* Default value of timeout


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
  /\ buf = 1     
  /\ \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver2 ==   
  /\ buf = 2     
  /\ \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver3 ==   
  /\ buf = 3     
  /\ \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver4 ==   
  /\ buf = 4     
  /\ \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver5 ==   
  /\ buf = 5     
  /\ \/ buf' = 4 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver6 ==   
  /\ buf = 6     
  /\ \/ buf' = 4 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver7 ==   
  /\ buf = 7     
  /\ \/ buf' = 6 \/ buf' = 5 \/ buf' = 4 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver8 ==   
  /\ buf = 8     
  /\ \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver9 ==   
  /\ buf = 9     
  /\ \/ buf' = 8 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver10 ==   
  /\ buf = 10     
  /\ \/ buf' = 8 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver11 ==   
  /\ buf = 11     
  /\ \/ buf' = 10 \/ buf' = 9 \/ buf' = 8 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver12 ==   
  /\ buf = 12     
  /\ \/ buf' = 8 \/ buf' = 4 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver13 ==   
  /\ buf = 13     
  /\ \/ buf' = 12 \/ buf' = 9 \/ buf' = 8 \/ buf' = 5 \/ buf' = 4 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver14 ==   
  /\ buf = 14     
  /\ \/ buf' = 12 \/ buf' = 10 \/ buf' = 8 \/ buf' = 6 \/ buf' = 4 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver15 ==   
  /\ buf = 15     
  /\ \/ buf' = 14 \/ buf' = 13 \/ buf' = 12 \/ buf' = 11 \/ buf' = 10 \/ buf' = 9 \/ buf' = 8 \/ buf' = 7 \/ buf' = 6 \/ buf' = 5 \/ buf' = 4 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver16 ==   
  /\ buf = 16     
  /\ \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver17 ==   
  /\ buf = 17     
  /\ \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver18 ==   
  /\ buf = 18     
  /\ \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver19 ==   
  /\ buf = 19     
  /\ \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver20 ==   
  /\ buf = 20     
  /\ \/ buf' = 4 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver21 ==   
  /\ buf = 21     
  /\ \/ buf' = 5 \/ buf' = 4 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver22 ==   
  /\ buf = 22     
  /\ \/ buf' = 6 \/ buf' = 4 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver23 ==   
  /\ buf = 23     
  /\ \/ buf' = 7 \/ buf' = 6 \/ buf' = 5 \/ buf' = 4 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver24 ==   
  /\ buf = 24     
  /\ \/ buf' = 8 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver25 ==   
  /\ buf = 25     
  /\ \/ buf' = 9 \/ buf' = 8 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver26 ==   
  /\ buf = 26     
  /\ \/ buf' = 10 \/ buf' = 8 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver27 ==   
  /\ buf = 27     
  /\ \/ buf' = 11 \/ buf' = 10 \/ buf' = 9 \/ buf' = 8 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver28 ==   
  /\ buf = 28     
  /\ \/ buf' = 12 \/ buf' = 8 \/ buf' = 4 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver29 ==   
  /\ buf = 29     
  /\ \/ buf' = 13 \/ buf' = 12 \/ buf' = 9 \/ buf' = 8 \/ buf' = 5 \/ buf' = 4 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver30 ==   
  /\ buf = 30     
  /\ \/ buf' = 14 \/ buf' = 12 \/ buf' = 10 \/ buf' = 8 \/ buf' = 6 \/ buf' = 4 \/ buf' = 2 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>

MsgDeliver31 ==   
  /\ buf = 31     
  /\ \/ buf' = 15 \/ buf' = 14 \/ buf' = 13 \/ buf' = 12 \/ buf' = 11 \/ buf' = 10 \/ buf' = 9 \/ buf' = 8 \/ buf' = 7 \/ buf' = 6 \/ buf' = 5 \/ buf' = 4 \/ buf' = 3 \/ buf' = 2 \/ buf' = 1 \/ buf' = 0 
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
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
          \/ MsgDeliver1  \/ MsgDeliver2  \/ MsgDeliver3  \/ MsgDeliver4  \/ MsgDeliver5  \/ MsgDeliver6  \/ MsgDeliver7  \/ MsgDeliver8  \/ MsgDeliver9  \/ MsgDeliver10  \/ MsgDeliver11  \/ MsgDeliver12  \/ MsgDeliver13  \/ MsgDeliver14  \/ MsgDeliver15  \/ MsgDeliver16  \/ MsgDeliver17  \/ MsgDeliver18  \/ MsgDeliver19  \/ MsgDeliver20  \/ MsgDeliver21  \/ MsgDeliver22  \/ MsgDeliver23  \/ MsgDeliver24  \/ MsgDeliver25  \/ MsgDeliver26  \/ MsgDeliver27  \/ MsgDeliver28  \/ MsgDeliver29  \/ MsgDeliver30  \/ MsgDeliver31 
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

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 16:40:30 CET 2021 by tran
\* Created Wed Jan 20 09:45:18 CET 2021 by tran
