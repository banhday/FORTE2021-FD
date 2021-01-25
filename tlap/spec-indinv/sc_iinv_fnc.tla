---------------------------- MODULE sc_iinv_fnc ----------------------------

EXTENDS Integers

CONSTANTS Phi, Delta             \* The bound on relaive process speed
ASSUME 1 <= Phi

ASSUME Delta >= 0

TODefault == 6*Phi + Delta       \* Default value of timeout
ASSUME TODefault >= 6*Phi + Delta

Action == { "SSched", "RSched", "IncMsgAge", "SSnd", "RNoSnd", "RRcv", "RComp" }
MsgAge == 0..Delta
Bufs == [ MsgAge -> BOOLEAN ]
   

VARIABLES suspected,      \* whether the receiver suspects the sender
          waitingTime,    \* how long the receiver has not heard from the sender                          
          timeout,        \* how long the receiver can wait for the sender                                                     
          sPC,            \* pc of the sender
          rPC,            \* pc of the receiver
          existsMsgOfAge,         \* the communication channel that is encoded with two bits 
                          \* in this specification                                                    
          sTimer,         \* how long the sender has not taken a step
          rTimer,         \* how long the sender has not taken a step    
          ePC,            \* pc of the environment
          hLFSC           \* how long it has been since the sender crashed
          
 
vars == << existsMsgOfAge, sTimer, rTimer, ePC, 
           suspected, waitingTime, timeout, sPC, rPC, 
           hLFSC >>          
              
\* The initialization              
Schedule_Init ==   
  /\ sTimer = 0
  /\ rTimer = 0
  /\ ePC = "SCrash"  
  /\ hLFSC = -1
  
         
Proc_Init ==
  /\ sPC = "SSnd" 
  /\ rPC = "RNoSnd"
  /\ existsMsgOfAge = [i \in MsgAge |-> FALSE ]       
  /\ suspected = FALSE
  /\ waitingTime = 0
  /\ timeout = TODefault   
  
Init == Proc_Init /\  Schedule_Init       

SCrash ==
  /\ ePC = "SCrash"
  /\ ePC' = "SSched"  
  /\ \/ /\ sPC # "SCrash"
        /\ sPC' = "SCrash"
        /\ sTimer' = 0
        /\ hLFSC' = 0
     \/ /\ UNCHANGED << sPC, sTimer >>
        /\ IF  hLFSC >= 0 /\ ~suspected
           THEN hLFSC' = hLFSC + 1
           ELSE UNCHANGED hLFSC                                    
  /\ UNCHANGED << existsMsgOfAge, rTimer, rPC,  
                        suspected, waitingTime, timeout >>
                       

SSched ==  
  /\ ePC = "SSched"
  /\ ePC' = "RSched"  
  /\ IF (sPC = "SSnd") 
     THEN /\ \/ /\ sTimer >= 2
                /\ sTimer' = 0          
                /\ UNCHANGED sPC                                                                         
             \/ /\ sTimer < 3 * Phi - 1
                /\ sTimer' =  sTimer + 1
                /\ UNCHANGED sPC                                       
          /\ UNCHANGED << existsMsgOfAge, rTimer, rPC,
                        suspected, waitingTime, timeout >>                                   
     ELSE UNCHANGED << existsMsgOfAge, sTimer, rTimer, sPC, rPC,  
                        suspected, waitingTime, timeout >>
  /\ UNCHANGED << hLFSC >>
  
                                                     
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
  /\ UNCHANGED << existsMsgOfAge, sTimer, sPC, 
                            suspected, waitingTime, timeout >>                  
  /\ UNCHANGED << hLFSC >>
  

IncMsgAge ==            
  /\ ePC = "IncMsgAge"
  /\ ePC' = "SSnd"    
  /\ IF Delta = 0
     THEN UNCHANGED existsMsgOfAge
     ELSE /\ existsMsgOfAge' \in Bufs
          /\ existsMsgOfAge'[Delta] = (existsMsgOfAge[Delta] \/ existsMsgOfAge[Delta - 1])
          /\ ~existsMsgOfAge'[0]
          /\ \A k \in 0..(Delta - 2) : existsMsgOfAge'[k + 1] = existsMsgOfAge[k]               
  /\ UNCHANGED << sTimer, rTimer,  
           suspected, waitingTime, timeout, sPC, rPC >>                                     
  /\ UNCHANGED << hLFSC >>
   

SSnd ==  
  /\ ePC = "SSnd"
  /\ ePC' = "RNoSnd"  
  /\ IF (sTimer = 0 /\ sPC = "SSnd")  \* whether the sender is active in the sub-round Send
     THEN existsMsgOfAge' = [ existsMsgOfAge EXCEPT ![0] = TRUE ]        
     ELSE UNCHANGED existsMsgOfAge
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC, suspected, waitingTime, timeout >>
  /\ UNCHANGED << hLFSC >>
  
  
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
  /\ UNCHANGED << hLFSC >>
           
           
MsgDeliver ==
  /\ \E k \in MsgAge : existsMsgOfAge[k]
  /\ existsMsgOfAge' \in Bufs
  /\ ~existsMsgOfAge'[Delta]
  /\ \E k \in MsgAge : existsMsgOfAge'[k] # existsMsgOfAge[k]
  /\ \A k \in MsgAge : existsMsgOfAge'[k] => existsMsgOfAge[k]          
  /\ waitingTime' = 0
  /\ IF suspected                     \* did the receiver suspect the sender?
     THEN /\ suspected' = FALSE       \* trust the sender again
          /\ timeout' = timeout + 1   \* increase the time out                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
  /\ UNCHANGED << hLFSC >>                                                   

NoMsgDeliver ==  
  /\ ~existsMsgOfAge[Delta]
  /\ UNCHANGED existsMsgOfAge
  /\ IF waitingTime < timeout
     THEN waitingTime' = waitingTime + 1
     ELSE UNCHANGED waitingTime                 
  /\ UNCHANGED << suspected, timeout, sTimer, rTimer, sPC, rPC >>       
  /\ UNCHANGED << hLFSC >>
  

RRcv ==
  /\ ePC = "RRcv"
  /\ ePC' = "RComp"
  /\ UNCHANGED << hLFSC >>
  /\ IF (rTimer = 0 /\ rPC = "RRcv")  \* is the receiver active in the sub-round Receive?
     THEN \/ MsgDeliver
          \/ NoMsgDeliver
     ELSE UNCHANGED << existsMsgOfAge, sTimer, rTimer,  
           suspected, waitingTime, timeout, sPC, rPC >>
  
     
             
RComp ==                         
  /\ ePC = "RComp"
  /\ ePC' = "SCrash"
  /\ UNCHANGED << hLFSC >>
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
  \/ SCrash
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
  /\ existsMsgOfAge \in Bufs
  /\ \E k \in 0..(3*Phi - 1) : sTimer = k 
  /\ \E k \in 0..(Phi - 1) : rTimer = k  
  /\ ePC \in {"SCrash", "SSched", "RSched", "IncMsgAge", "SSnd",  
                  "RNoSnd", "RRcv", "RComp"}  
  /\ suspected \in BOOLEAN
  /\ timeout = 6 * Phi + Delta 
  /\ waitingTime \in 0..timeout
  /\ suspected => waitingTime >= timeout     
  /\ sPC \in {"SSnd", "SCrash"} 
  /\ rPC \in {"RNoSnd", "RRcv", "RComp"}
  /\ \E k \in -1..((3 * Phi + Delta) + Phi * TODefault + (3 * Phi))  : hLFSC = k 
  /\ sPC = "SSnd" <=> hLFSC = -1
  /\ sPC = "SCrash" <=> (hLFSC >= 0 /\ sTimer = 0)  
  
  
  
StrongCompleteness ==  
  /\ timeout >= 6 * Phi + Delta =>
                hLFSC <= (3 * Phi + Delta) + Phi * timeout + (3 * Phi) 
  /\ hLFSC >= (3 * Phi + Delta) + Phi * timeout + (3 * Phi) => 
                (suspected /\ sPC = "SCrash")
  /\ (timeout >= 6 * Phi + Delta /\ waitingTime = timeout) =>
                (sPC = "SCrash" /\
                 \A k \in MsgAge : ~existsMsgOfAge[k])  
  /\ (timeout >= 6 * Phi + Delta /\ waitingTime > timeout) =>
                (sPC = "SCrash" /\
                 \A k \in MsgAge : ~existsMsgOfAge[k]) 
                 
Constraint3 ==
  ((\A k \in MsgAge : ~existsMsgOfAge[k]) /\
                waitingTime > 0 /\
                waitingTime < 3 * Phi) =>
                    ( (sPC = "SSnd"   /\ sTimer >= waitingTime) \/
                      (sPC = "SCrash" /\ sTimer = 0) ) 
                      
Constraint4 ==                      
  (3 * Phi  <= waitingTime /\ waitingTime < 3 * Phi + Delta) =>
                ((\E k \in MsgAge : waitingTime <= 3 * Phi + k /\ existsMsgOfAge[k]) \/
                 (sPC = "SCrash" /\ \A k \in MsgAge : ~existsMsgOfAge[k]))
                 
                 
Constraint5 ==                 
  waitingTime >= 3 * Phi + Delta =>
                ((existsMsgOfAge[Delta]) \/
                 ((sPC = "SCrash") /\ 
                  (\A k \in MsgAge : ~existsMsgOfAge[k])))
                  
                  
Constraint6 ==
  ( (( waitingTime >= 5 * Phi + Delta /\
       (\E k \in MsgAge : existsMsgOfAge[k]) ) => 
              ( (rTimer >= waitingTime - 5 * Phi - Delta) /\
                rPC = "RNoSnd" )) /\
    (( waitingTime >= 4 * Phi + Delta /\
       waitingTime <  5 * Phi + Delta /\
       (\E k \in MsgAge : existsMsgOfAge[k]) ) =>
              ( (rPC = "RNoSnd" \/ rPC = "RComp") /\
                (rPC = "RComp" => rTimer >= waitingTime - 4 * Phi - Delta))) /\
    (( waitingTime >= 3 * Phi + Delta /\
       waitingTime <  4 * Phi + Delta /\
       (\E k \in MsgAge : existsMsgOfAge[k]) ) =>
              ( (rPC = "RNoSnd" \/ rPC = "RComp" \/ rPC = "RRcv" ) /\
                (rPC = "RRcv" => rTimer >= waitingTime - 3 * Phi - Delta))))  \/
  ( (\A k \in MsgAge : ~existsMsgOfAge[k]) /\
    waitingTime >= 3 * Phi + Delta /\
    sPC = "SCrash" )
    
    
Constraint7 ==
  /\ (hLFSC >= 0 /\ hLFSC < Delta) => 
            ((\E k \in MsgAge : existsMsgOfAge[k]) => 
                (\A k \in MsgAge : k <= hLFSC => ~existsMsgOfAge[k]))                                                              
  /\ hLFSC >= Delta =>
            (((existsMsgOfAge[Delta]) /\
              (\A k \in MsgAge : k < Delta => ~existsMsgOfAge[k])) \/ 
             (\A k \in MsgAge : ~existsMsgOfAge[k]))
             
Constraint8 == 
  /\ hLFSC >= 3 * Phi + Delta => 
                (\A k \in MsgAge : ~existsMsgOfAge[k])                

  /\ (( hLFSC >= 2 * Phi + Delta /\
             (\E k \in MsgAge : existsMsgOfAge[k]) ) => 
                    ( rTimer >= hLFSC - 2 * Phi - Delta /\ 
                      rPC = "RNoSnd" ))
  /\ (( hLFSC >= Phi + Delta /\
             hLFSC <  2 * Phi + Delta /\
             (\E k \in MsgAge : existsMsgOfAge[k]) ) =>
                    ( ( rPC = "RNoSnd" \/ rPC = "RComp") /\
                      ( rPC = "RComp" => rTimer >= hLFSC - Phi - Delta)) )                
  /\ ( hLFSC >= Delta /\
            hLFSC <  Phi + Delta /\
            (\E k \in MsgAge : existsMsgOfAge[k]) ) =>
                    (rPC = "RRcv" => rTimer >= hLFSC - Delta)
  /\ hLFSC >= 3 * Phi + Delta => 
                (\A k \in MsgAge : ~existsMsgOfAge[k])
                
Constraint9A ==
  /\ ( hLFSC > 3 * Phi + Delta /\
            hLFSC < (3 * Phi + Delta) + Phi * timeout /\
            ~suspected /\
            waitingTime < timeout ) =>
                (hLFSC <= (3 * Phi + Delta) + Phi * waitingTime + rTimer)
                  
Constraint9B ==
  /\ (hLFSC > (3 * Phi + Delta) + Phi * timeout /\
            ~suspected) =>
                waitingTime >= timeout
  
Constraint9C ==
  /\  ((hLFSC = (3 * Phi + Delta) + Phi * timeout - 1 /\
            ~suspected) =>
                ((waitingTime = 6 * Phi + Delta - 1 /\ rTimer = Phi - 1) \/ 
                 (waitingTime = 6 * Phi + Delta))) /\
           (hLFSC >= (3 * Phi + Delta) + Phi * timeout /\
            ~suspected) =>
                waitingTime >= timeout
                
Constraint9 == 
  Constraint9A /\ Constraint9B /\ Constraint9C  
                
Constraint10 ==
  /\ (( hLFSC >= 3 * Phi + Delta + Phi * timeout + 2*Phi /\
             ~suspected ) => 
                ( rTimer >= hLFSC - (3 * Phi + Delta + Phi * timeout) - 2*Phi /\
                  rPC = "RRcv" ))
  /\ (( hLFSC >= 3 * Phi + Delta + Phi * timeout + Phi /\
             hLFSC <  3 * Phi + Delta + Phi * timeout + 2*Phi /\ 
             ~suspected ) =>
                ( (rPC = "RNoSnd" \/ rPC = "RRcv") /\
                  (rPC = "RNoSnd" => rTimer >= hLFSC - (3 * Phi + Delta + Phi * timeout) - Phi)) )
  /\ (( hLFSC >= 3 * Phi + Delta + Phi * timeout /\
             hLFSC <  3 * Phi + Delta + Phi * timeout + Phi /\
             ~suspected ) =>
                ( (rPC = "RNoSnd" \/ rPC = "RComp" \/ rPC = "RRcv") /\
                  (rPC = "RComp" => rTimer >= hLFSC - (3 * Phi + Delta + Phi * timeout)) ))
                                                                                                      
ConstraintsInIndInv_BigStep ==
  /\ TypeOK
  /\ StrongCompleteness
  /\ Constraint3
  /\ Constraint4
  /\ Constraint5
  /\ Constraint6
  /\ Constraint7
  /\ Constraint8
  /\ Constraint9
  /\ Constraint10
  

IndInv_BigTODefault ==
  \/ ePC # "SCrash"
  \/ ConstraintsInIndInv_BigStep
  
Init_IndInv_BigTODefault ==
  /\ ePC = "SCrash"
  /\ ConstraintsInIndInv_BigStep  

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 17:31:01 CET 2021 by tran
\* Created Wed Jan 20 07:31:23 CET 2021 by tran
