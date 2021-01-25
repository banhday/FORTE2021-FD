---------------------------- MODULE sc_iinv_cntr_d2 ----------------------------

EXTENDS Integers

CONSTANTS Phi             \* The bound on relaive process speed
ASSUME 1 <= Phi

Delta == 2
TODefault == 6*Phi + Delta       \* Default value of timeout

ASSUME TODefault >= 6*Phi + Delta

MAX_TIME == 2 * ( 6 * Phi + Delta + 1 ) + 3 * Phi * (6 * Phi + Delta + 1)

Action == { "SCrash", "SSched", "RSched", "IncMsgAge", "SSnd", "RNoSnd", "RRcv", "RComp" }
MsgAge == 0..Delta   

VARIABLES suspected,      \* whether the receiver suspects the sender
          waitingTime,    \* how long the receiver has not heard from the sender                          
          timeout,        \* how long the receiver can wait for the sender                                                     
          sPC,            \* pc of the sender
          rPC,            \* pc of the receiver
          buf,         \* the communication channel that is encoded with two bits 
                          \* in this specification                                                    
          sTimer,         \* how long the sender has not taken a step
          rTimer,         \* how long the sender has not taken a step    
          ePC,            \* pc of the environment
          hLFSC
 
vars == << buf, sTimer, rTimer, ePC, hLFSC,
           suspected, waitingTime, timeout, sPC, rPC >>          
              
\* The initialization              
Schedule_Init ==   
  /\ sTimer = 0
  /\ rTimer = 0
  /\ ePC = "SCrash"
  /\ hLFSC = -1
  
         
Proc_Init ==
  /\ sPC = "SSnd" 
  /\ rPC = "RComp"
  /\ buf = 0       
  /\ suspected = FALSE
  /\ waitingTime = 0
  /\ timeout = TODefault   
  
Init == Proc_Init /\  Schedule_Init       

SCrash ==
  /\ ePC = "SCrash"
  /\ ePC' = "SSched"
  /\ IF hLFSC >= 0 /\ ~suspected
     THEN hLFSC' = hLFSC + 1
     ELSE UNCHANGED hLFSC
  /\ IF sPC # "SCrash" 
     THEN \/ /\ sPC' = "SCrash"       
             /\ sTimer' = 0         \* reset sTimer to reduce the state space
             /\ hLFSC' = 0             
             /\ UNCHANGED << buf, rTimer, rPC,   
                              suspected, waitingTime, timeout >>  
          \/ UNCHANGED << buf, sTimer, rTimer, sPC, rPC, 
                      suspected, waitingTime, timeout >>  
     ELSE UNCHANGED << buf, sTimer, rTimer, sPC, rPC, 
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
          /\ UNCHANGED << buf, rTimer, rPC,
                        suspected, waitingTime, timeout >>                                   
     ELSE UNCHANGED << buf, sTimer, rTimer, sPC, rPC,  
                        suspected, waitingTime, timeout >>
  /\ UNCHANGED hLFSC
                                                 
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
  /\ UNCHANGED << hLFSC >>
  

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
  /\ UNCHANGED hLFSC
  
SSnd ==  
  /\ ePC = "SSnd"
  /\ ePC' = "RNoSnd"  
  /\ IF (sTimer = 0 /\ sPC = "SSnd")  \* whether the sender is active in the sub-round Send
     THEN buf' = buf + 1              \* add a new message to the communication channel        
     ELSE UNCHANGED buf
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC, suspected, waitingTime, timeout >>
  /\ UNCHANGED hLFSC
  
                      
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
  /\ UNCHANGED hLFSC


MsgDeliver1 ==   
  /\ buf = 1
  /\ buf' = 0                         
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
  

MsgDeliver2 ==   
  /\ buf = 2
  /\ buf' = 0                         
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
  /\ buf = 4
  /\ buf' = 0                            
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>   
  

MsgDeliver5 ==   
  /\ buf = 5
  /\ \/ buf' = 0   
     \/ buf' = 1                            
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>
  

MsgDeliver6 ==   
  /\ buf = 6
  /\ \/ buf' = 0
     \/ buf' = 2                            
  /\ waitingTime' = 0
  /\ IF suspected
     THEN /\ suspected' = FALSE
          /\ timeout' = timeout + 1                                              
     ELSE UNCHANGED << suspected, timeout >> 
  /\ UNCHANGED << sTimer, rTimer, sPC, rPC >>  
  

MsgDeliver7 ==   
  /\ buf = 7
  /\ \/ buf' = 0
     \/ buf' = 1
     \/ buf' = 2
     \/ buf' = 3                            
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
  /\ UNCHANGED hLFSC     
             
   
RComp ==                         
  /\ ePC = "RComp"
  /\ ePC' = "SCrash"  
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
  /\ UNCHANGED hLFSC


Next == 
  \/ SCrash
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
  
               
TypeOK ==    
  /\ buf \in 0..(2^(Delta + 1) - 1)
  /\ sTimer \in 0..(3*Phi - 1)
  /\ rTimer \in 0..(Phi - 1)
  /\ ePC \in {"SCrash", "SSched", "RSched", "IncMsgAge", "SSnd",  
                  "RNoSnd", "RRcv", "RComp"}  
  /\ suspected \in BOOLEAN
  /\ timeout = 6 * Phi + Delta 
  /\ waitingTime \in 0..timeout
  /\ suspected => waitingTime >= timeout     
  /\ sPC \in {"SSnd", "SCrash"} 
  /\ rPC \in {"RNoSnd", "RRcv", "RComp"}
  /\ hLFSC \in -1..((3 * Phi + Delta) + Phi * timeout + (3 * Phi))  
  /\ sPC = "SSnd" <=> hLFSC = -1
  /\ sPC = "SCrash" <=> (hLFSC >= 0 /\ sTimer = 0) 
  

StrongCompleteness ==  
  /\ timeout >= 6 * Phi + Delta =>
                hLFSC <= (3 * Phi + Delta) + Phi * timeout + (3 * Phi) 
  /\ hLFSC >= (3 * Phi + Delta) + Phi * timeout + (3 * Phi) => 
                (suspected /\ sPC = "SCrash")
  /\ (timeout >= 6 * Phi + Delta /\ waitingTime = timeout) =>
                (sPC = "SCrash" /\ buf = 0)  
  /\ (timeout >= 6 * Phi + Delta /\ waitingTime > timeout) =>
                (sPC = "SCrash" /\ buf = 0)   
                
                
Constraint3 ==
  ( /\ buf = 0 
    /\ waitingTime > 0 
    /\ waitingTime < 3 * Phi) =>
          ( (sPC = "SSnd"   /\ sTimer >= waitingTime) \/
            (sPC = "SCrash" /\ sTimer = 0) )  
      
            
Constraint4 ==                      
  (3 * Phi  <= waitingTime /\ waitingTime < 3 * Phi + Delta) =>
      ((\E k \in MsgAge : waitingTime <= 3 * Phi + k /\ buf >= 2^k) \/
       (sPC = "SCrash" /\ buf = 0))                           
      
      
Constraint5 ==                 
  waitingTime >= 3 * Phi + Delta =>
                ( \/ buf >= 2^Delta
                  \/ (sPC = "SCrash" /\ buf = 0))
                  
                  
Constraint6 ==
  ( (( waitingTime >= 5 * Phi + Delta /\
       buf > 0 ) => 
              ( (rTimer >= waitingTime - 5 * Phi - Delta) /\
                rPC = "RNoSnd" )) /\
    (( waitingTime >= 4 * Phi + Delta /\
       waitingTime <  5 * Phi + Delta /\
       buf > 0 ) =>
              ( (rPC = "RNoSnd" \/ rPC = "RComp") /\
                (rPC = "RComp" => rTimer >= waitingTime - 4 * Phi - Delta))) /\
    (( waitingTime >= 3 * Phi + Delta /\
       waitingTime <  4 * Phi + Delta /\
       buf > 0 ) =>
              ( (rPC = "RNoSnd" \/ rPC = "RComp" \/ rPC = "RRcv" ) /\
                (rPC = "RRcv" => rTimer >= waitingTime - 3 * Phi - Delta))))  \/
  ( buf = 0 /\
    waitingTime >= 3 * Phi + Delta /\
    sPC = "SCrash" )         
    
             
Constraint7 ==
  /\ (hLFSC >= 0 /\ hLFSC < Delta) => 
            (buf > 0 => buf = 0)                                                              
  /\ hLFSC >= Delta =>
            ((buf >= 2^Delta /\ buf = 0) \/ 
              buf = 0)             
                  
                        
Constraint8 == 
  /\ hLFSC >= 3 * Phi + Delta => buf = 0               

  /\ (( hLFSC >= 2 * Phi + Delta /\
             buf > 0 ) => 
                    ( rTimer >= hLFSC - 2 * Phi - Delta /\ 
                      rPC = "RNoSnd" ))
  /\ (( hLFSC >= Phi + Delta /\
             hLFSC <  2 * Phi + Delta /\
             buf > 0 ) =>
                    ( ( rPC = "RNoSnd" \/ rPC = "RComp") /\
                      ( rPC = "RComp" => rTimer >= hLFSC - Phi - Delta)) )                
  /\ ( hLFSC >= Delta /\
            hLFSC <  Phi + Delta /\
            buf > 0 ) =>
                    (rPC = "RRcv" => rTimer >= hLFSC - Delta)
  /\ hLFSC >= 3 * Phi + Delta => buf = 0    
  

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
\* Last modified Thu Jan 21 11:15:24 CET 2021 by tran
\* Created Wed Jan 20 20:37:36 CET 2021 by tran
