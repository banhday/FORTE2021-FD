------------------------------ MODULE EPFD96 ------------------------------

(* A TLA+ encoding of the eventually perfect failure detectors in Figure 10 [1] 
   under partially synchronous constraints of the DLS computational model [2].  
  
   [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for 
   reliable distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.
   
   [2] Dwork, Cynthia, Nancy Lynch, and Larry Stockmeyer. "Consensus in the presence 
   of partial synchrony." Journal of the ACM (JACM) 35.2 (1988): 288-323.                                                                 
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2019
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE. 
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N,            \* The number of processes  
          T,            \* The maximum number of failures
          F,            \* The current number of failures  
          Delta,        \* Bound for message delay
          Phi           \* Bound for relaive process speed
  

\* For the model checker APALACHE
a <: b == a

Proc == 1..N            \* Set of processes, and process IDs are from 1 to N

\* If Delta = 0 and Phi = 1, the computational model is asynchronous.
ASSUME 0 <= Delta /\ 1 <= Phi
 
\*  - After the time point T_0, ages of messages in transit are eventually  
\*  limited by (Delta + 6 * Phi). 
\*  - However, we can apply an abstraction on message ages. After an message 
\*  reaches Delta years old, we can stop increasing its age.
\*  - Assume that new messages are 0 years old.
\*  - Therefore, possible message ages range from 0 to Delta. 
MsgAge == 0..Delta       
 
\*  - My inductive invariant is checked with TOGuard = 3 * Phi + Delta + 2.
\*  The reason of this change is that a time-out never changes since it reaches 
\*  3 * Phi + Delta + 2. 
\*  - Notice that the mimimal upper bound of time-outs might be less.
\*  - Here we set TODefault is 1. In an execution, a time-out might be increased.
TOGuard == 3 * Phi + Delta + 2  
TODefault == 1 

\*  - For every process, there is a clock to measure how long it has not take
\*  a transition. These clocks are declared later as an array "break_timer".
\*  In every global step, every clock is increased by 1, or reset to 0. When
\*  break_timer[i] reaches Phi - 1, it will be reset to 0 in the next step.
\*  If break_timer[i] = 0 and process i is correct, it must take a transition
\*  in this logically global step.
\*  - A break timer of a crashed process is always 0.    
\*  - Break_Period is a set of possible values of break_timer[i] for every i.
\*  Hence, break_timer has a type invariant [Proc -> Break_Period].     
Break_Period == 0..(Phi - 1)


Action == {"send", "del", "comp", "crash"}                \* Transition names
 
\*  - MsgAgePowerSet is a set of two dimensional matrixs who are possible 
\*  configuration of message channels. 
\*  - The value of MsgAgePowerSet is cached and never computed again in the 
\*  running time of TLC.
\*  - MsgAgePowerSet is used to non-deterministically deliver in-transit messages.   
MsgAgePowerSet == [Proc \times Proc -> SUBSET (0..Delta)]


  
\* Algorithm's variables  
VARIABLES suspected,    \* Two dimenstional matrix has type [Proc \times Proc -> BOOL]
          waiting_time, \* Two dimenstional matrix has type [Proc \times Proc -> Int] 
                        \* How long a process p_i has waited for process p_j
          time_out,     \* Two dimenstional matrix has type [Proc \times Proc -> Int]
                        \* The time-out value for how long process p_i waits for process p_j
          pc            \* Describe transitions which processes take 
          
\* Model's variables          
VARIABLES msgBuf,       \* Two dimensional matrix contains ages of messages sent 
                        \* from process p_i to process p_j.                     
          del,          \* Whether a process p_i received any messages from
                        \* process p_j in the last execution of Receive.           
          break_timer,  \* How long a process has not take a transition 
          phase         \* 4 phases: schedule, send, receive, and compute
          
\* The below variable fromLastSend  is a ghost one. It is used only to construct 
\* an inductive invariant. In this encoding, you do not need to care about it. 
\* VARIABLES fromLastSend          

vars == << del, msgBuf, break_timer, phase, 
           suspected, waiting_time, time_out, pc >>          
             
  
\*  - Initialize the enviromental variables.
\*  - The first transition is a scheduling step.
Scheduler_Init == 
  /\ pc \in [Proc -> Action]
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) <= F
  /\ break_timer \in [Proc -> Break_Period]
  /\ \A p \in Proc : IF pc[p] = "crash"
                     THEN break_timer[p] = 0
                     ELSE break_timer[p] < Phi  
  /\ phase = "sched"  
               

\*  - Initialize process variables.
\*  - If a process is crashed, set its time-outs to 0. Otherwise, set 1.          
Proc_Init ==
  /\ msgBuf = [<< p, q >> \in Proc \times Proc |-> {} <: {Int} ]       
  /\ suspected = [<< p, q >> \in Proc \times Proc |-> FALSE]
  /\ waiting_time = [<< rcver, snder >> \in Proc \times Proc |-> 0 ]
  /\ time_out = [<< p, q >> \in Proc \times Proc |-> IF pc[p] = "crash" \/ p = q 
                                                     THEN 0
                                                     ELSE TODefault ]
  /\ del = [<< p, q >> \in Proc \times Proc |-> FALSE]                  

  
\* Initial states 
Init == Scheduler_Init /\ Proc_Init 

\*  - Schedule the movement of processes. 
\*  - If break_timer'[i] # 0, process p_i is frozen in the next global transition. 
\*  - If process i is already crashed, then break_timer[i] = 0.
\*  - In this encoding, a global transition contains four phases: schedule, send, 
\*  deliver, and comp whose order is fixed: sched -> send -> del -> comp. 
\*  - A global transition is sometimes called as a big step, and phases are called 
\*  small steps. 
Schedule ==  
  /\ phase = "sched"
  /\ phase' = "send"  
  /\ \E aliveProc \in SUBSET { p \in Proc : pc[p] # "crash" } :  \* correct processes
        /\ Cardinality(aliveProc) >= N - F   
        /\ \E activeProc \in SUBSET aliveProc :         \* arbitrarily active processes         
              /\ pc' = [p \in Proc |-> 
                          IF p \notin aliveProc
                          THEN "crash"
                          ELSE IF p \notin activeProc 
                          THEN pc[p]
                          ELSE IF pc[p] = "send" 
                          THEN  "del"
                          ELSE IF pc[p] = "del"
                          THEN "comp"
                          ELSE "send"]    
          /\ break_timer' = [ p \in Proc |-> IF p \notin aliveProc   
                                             THEN 0 
                                             ELSE IF p \in activeProc
                                             THEN 0
                                             ELSE break_timer[p] + 1]
                                          
       
\* Increase every age by 1. This udpate is done in the "sched" phase.                                                                                    
\* All process variables are unchanged.           
AgeIncrease ==                                         
  msgBuf' = [<< p, q >> \in Proc \times Proc |-> 
                   IF pc'[q] = "crash"
                   THEN {}
                   ELSE {IF k < Delta THEN k + 1 ELSE Delta: k \in msgBuf[p, q]}]     
   
\* Update the configuration because of recently crashed processes.     
UponCrash ==
  /\ time_out' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN 0
                        ELSE time_out[p, q]]
  /\ waiting_time' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN 0
                        ELSE waiting_time[p, q]]
  /\ suspected' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN FALSE
                        ELSE suspected[p, q]]  
                                                                 
\*  - Messages sent to crashed processes are ignored.
\*  - Here we assume that new messages are 0 year old. Only active processes in 
\*  the phase "send" can add 0 in message buffers.
\*  - Other variables are unchanged.                                                                                                                                                             
AddNewMsgs ==
  /\ phase = "send"
  /\ phase' = "del" 
  /\ msgBuf' = [<< snder, rcver >> \in Proc \times Proc |->     
                    IF pc[rcver] = "crash"  
                    THEN {}        
                    ELSE IF /\ pc[snder] = "send" 
                            /\ break_timer[snder] = 0 
                            /\ rcver # snder
                    THEN { 0 } \cup msgBuf[snder, rcver] 
                    ELSE msgBuf[snder, rcver] ]
  /\ UNCHANGED << pc, break_timer, del >>
     
\* Only increase waiting time  
UponSend ==                
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash" \/ p = q   
                            THEN 0
                            ELSE IF /\ pc[p] = "send" 
                                    /\ break_timer[p] = 0 
                                    /\ waiting_time[p, q] < time_out[p, q]
                            THEN waiting_time[p, q] + 1
                            ELSE waiting_time[p, q]]
  /\ UNCHANGED << suspected, time_out >>                           
   
\*  - For every pair of processes <<snder, rcver>>, remove an arbitrary set of 
\*  messages in msgBuf[snder, rcver]. The obtained result must satisfy partially 
\*  synchronous constraints. Messages sent to crashed processes are ignored.
\*  - Set del'[rcver, snder] = msgBuf'[snder, rcver] # msgBuf[snder, rcver] for 
\*  every snder, for every active "del" rcver. We do not need to know what messages 
\*  have been delivered.  
Deliver ==
  /\ phase = "del"
  /\ phase' = "comp"     
  /\ msgBuf' \in MsgAgePowerSet 
  /\ \A snder, rcver \in Proc : 
          IF pc[rcver] = "crash"
          THEN msgBuf'[snder, rcver] = {}
          ELSE IF pc[rcver] = "del" /\ break_timer[rcver] = 0
          THEN /\ msgBuf'[snder, rcver] \subseteq msgBuf[snder, rcver]
               /\ \A k \in msgBuf'[snder, rcver] : k < Delta 
          ELSE msgBuf'[snder, rcver] = msgBuf[snder, rcver]      
  /\ del' = [<< rcver, snder >> \in Proc \times Proc |->
                    IF pc[rcver] = "crash" \/ rcver = snder                                                            
                    THEN FALSE                    
                    ELSE IF pc[rcver] = "del" /\ break_timer[rcver] = 0 
                    THEN msgBuf'[snder, rcver] # msgBuf[snder, rcver]                           
                    ELSE del[rcver, snder] ] 
  /\ UNCHANGED << pc, break_timer >>
                      
\*  - If an active rcver has not received any messages from a snder in this step,  
\*  and has waited for snder less than time_out[rcver, snder], then it increases 
\*  waiting_time[rcver, snder] by 1. If waiting-time[rcver, snder] already equals
\*  to time-out[rcver, snder], the waiting time is unchanged. This optimization 
\*  is used to reduced the number of states.
\*  - If received some message from a suspected process, update the prediction,
\*  and increase the timeout.                      
UponReceive ==                                          
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash" \/ p = q
                            THEN 0
                            ELSE IF pc[p] = "del"/\ break_timer[p] = 0  
                            THEN IF del'[p, q] 
                                 THEN 0
                                 ELSE IF waiting_time[p, q] < time_out[p, q] 
                                 THEN waiting_time[p, q] + 1           
                                 ELSE waiting_time[p, q]
                            ELSE waiting_time[p, q]]      
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                            CASE pc[p] = "crash" ->  
                                    FALSE
                              [] pc[p] = "del" /\ break_timer[p] = 0 /\ del'[p, q] /\ suspected[p, q] -> 
                                    FALSE
                              [] OTHER -> 
                                    suspected[p, q] ]                                  
  /\ time_out' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"   
                            THEN 0
                            ELSE IF /\ pc[p] = "del" 
                                    /\ break_timer[p] = 0
                                    /\ suspected[p, q]                                    
                                    /\ ~suspected'[p, q]  
                            THEN time_out[p, q] + 1
                            ELSE time_out[p, q]]   
    
      
\*  - If the waiting time equals the time-out, change the predicition.
\*  - Update the waiting time.    
Comp ==
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                      CASE pc[p] = "crash" ->  
                                FALSE
                        [] /\ pc[p] = "comp" 
                           /\ p # q
                           /\ break_timer[p] = 0 
                           /\ ~del[p, q] 
                           /\ waiting_time[p, q] = time_out[p, q] -> 
                                TRUE
                        [] OTHER -> 
                                suspected[p, q] ]
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash" \/ p = q   
                            THEN 0
                            ELSE IF /\ pc[p] = "comp" 
                                    /\ break_timer[p] = 0 
                                    /\ waiting_time[p, q] < time_out[p, q]
                                    /\ ~suspected'[p, q]
                            THEN waiting_time[p, q] + 1
                            ELSE waiting_time[p, q]]                                    
  /\ UNCHANGED << time_out >>                               
  
  
\* Partially synchronous constraint for relative process speed. This constraint
\* is checked in only the scheduling step.          
PhiConstraint == 
  \A i \in Proc : pc'[i] # "crash" => /\ 0 <= break_timer'[i] 
                                      /\ break_timer'[i] < Phi
                                  
\* Partially synchronous constraint for message delay. This constraint is checked
\* in only the delivery step.
DeltaConstraint ==
  phase = "del" => 
      (\A rcver \in Proc : 
               (pc[rcver] = "del" /\ break_timer[rcver] = 0) 
            => (\A snder \in Proc : \A k \in msgBuf'[snder, rcver] : k < Delta))   
                                        

\* Constraints on behaviors of crashed processes: their speed, predictions and  
\* upcoming messages can be ignored. Similar to PhiConstraint, this contraint
\* is checked in only the scheduling step.  
CrashConstraint ==
  /\ Cardinality({p \in Proc : pc'[p] = "crash"}) <= F
  /\ \A p \in Proc : 
        pc'[p] = "crash"  
            => /\ break_timer'[p] = 0
               /\ \A q \in Proc : /\ del'[p, q] = FALSE                                                                    
                                  /\ msgBuf'[q, p] = {}    
  
\* Transitions                                             
Next == 
  \/ /\ Schedule          \* Mark a subset of Proc as active ones               
     /\ PhiConstraint     \* A new schedule must satisfy Phi and                               
     /\ AgeIncrease       \* Move to a next time point
     /\ UNCHANGED del     \* No delivery in the schedule step
     /\ CrashConstraint   \* Crash constraints              
     /\ UponCrash         \* Only for crashed processes     
  \/ /\ AddNewMsgs        \* New messages appear in the message buffers
     /\ UponSend          \* Only increase wating time        
  \/ /\ Deliver           \* Deliver messages
     /\ DeltaConstraint   \* Check the Delta constraint                         
     /\ UponReceive       \* Update failure detectors based on incoming messages                     
  \/ /\ phase = "comp"    \* The environment updates only the variable phase
     /\ phase' = "sched"
     /\ UNCHANGED << msgBuf, del, pc, break_timer >>
     /\ Comp               
               
               
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


  
\* Type information - very simple ones
TypeOK ==
  /\ pc \in [Proc -> Action]
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) <= F
  /\ del \in [Proc \times Proc -> BOOLEAN]  
  /\ msgBuf \in [Proc \times Proc -> SUBSET Int]
  /\ phase \in {"sched", "send", "del", "comp"}
  /\ break_timer \in [Proc -> Int] 
  /\ waiting_time \in [ Proc \times Proc -> Int]
  /\ suspected \in [Proc \times Proc -> BOOLEAN]  
  /\ time_out \in [ Proc \times Proc -> Int]

\* More complex constraints on possible values of variables             
ComplexTypeInfo ==
  /\ msgBuf \in [ Proc \times Proc -> SUBSET MsgAge ]
  /\ \A rcver \in Proc : 
          IF pc[rcver] = "crash"  
          THEN \A snder \in Proc : 
                      /\ msgBuf[snder, rcver] = {}
                      /\ time_out[rcver, snder] = 0
                      /\ waiting_time[rcver, snder] = 0
                      /\ ~del[rcver, snder]              
                      /\ ~suspected[rcver, snder]  
                      /\ break_timer[rcver] = 0
          ELSE \A snder \in Proc : 
                      IF snder = rcver
                      THEN msgBuf[snder, rcver] = {}
                      ELSE \A k \in msgBuf[snder, rcver] : k < Delta + 3 * Phi  
  /\ \A rcver \in Proc : 
        ((phase = "comp" /\ pc[rcver] = "del" /\ break_timer[rcver] = 0)
            => (\A snder \in Proc : \A k \in msgBuf[snder, rcver] : /\ 0 <= k 
                                                                    /\ k < Delta))       
  /\ break_timer \in [ Proc -> Break_Period ]  
  /\ \A p \in Proc : IF pc[p] = "crash"
                     THEN break_timer[p] = 0
                     ELSE break_timer[p] < Phi  
  /\ suspected \in [Proc \times Proc -> BOOLEAN]  
  /\ \A p, q \in Proc : pc[p] = "crash" => suspected[p, q] = FALSE
  /\ time_out \in [ Proc \times Proc -> 0..TOGuard]
  /\ \A p, q \in Proc : pc[p] = "crash" => time_out[p, q] = 0
  /\ \A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash")
                            => (time_out[p, q] # 0)
  /\ waiting_time \in [ Proc \times Proc -> 0..TOGuard]
                                              
                
\* Eventually every process that crashes is permanently suspected by every correct 
\* process.
StrongCompleteness == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] = "crash") => suspected[p, q])

\* There is a time after which correct processes are not suspected by any correct 
\* process. 
EventualStrongAccuracy == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash") => ~suspected[p, q])

  
=============================================================================
\* Modification History
\* Last modified Thu Dec 05 15:02:46 CET 2019 by tthai
\* Created Wed Nov 06 10:37:10 CET 2019 by tthai

