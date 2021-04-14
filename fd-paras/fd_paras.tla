--------------------------- MODULE sa_fnc_paras ---------------------------

(* A TLA+ encoding of the eventually perfect failure detectors in Figure 10 [1] 
   under partially synchronous constraints of the DLS computational model [2].  
  
   [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for 
   reliable distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.
   
   [2] Dwork, Cynthia, Nancy Lynch, and Larry Stockmeyer. "Consensus in the presence 
   of partial synchrony." Journal of the ACM (JACM) 35.2 (1988): 288-323.                                                                 
  
   Thanh-Hai Tran, Igor Konnov, Josef Widder, 2019
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE. 
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N,                  \* The number of processes  
          T,                  \* The maximum number of failures
          F,                  \* The current number of failures  
          Delta,              \* Bound for message delay
          Phi                 \* Bound for relaive process speed
ASSUME 0 <= Delta /\ 1 <= Phi
          
Proc == 1..N                  \* Set of processes
TODefault == 6*Phi + Delta    \* Default value of timeout
MsgAge == 0..Delta            \* Set of message ages                                 
MsgAgePowerSet == [ Proc \times Proc -> [ MsgAge -> BOOLEAN ]]


Action == {"send", "del", "comp", "crash"}                \* Transition names
 
 
\* Algorithm's variables  
VARIABLES suspected,    \* Two dimenstional matrix has type [Proc \times Proc -> BOOL]
          waiting_time, \* Two dimenstional matrix has type [Proc \times Proc -> Int] 
                        \* How long a process p_i has waited for process p_j
          timeout,      \* Two dimenstional matrix has type [Proc \times Proc -> Int]
                        \* The time-out value for how long process p_i waits for 
                        \* process p_j
          pc            \* Describe transitions which processes take 
          
\* Model's variables          
VARIABLES existMsgOfAge,       \* Two dimensional matrix contains ages of messages sent 
                        \* from process p_i to process p_j.                     
          del,          \* Whether a process p_i received any messages from
                        \* process p_j in the last execution of Receive.           
          timer,  \* How long a process has not take a transition 
          subround         \* 4 subrounds: schedule, send, receive, and compute
          
vars == << del, existMsgOfAge, timer, subround, 
           suspected, waiting_time, timeout, pc >>          
             
  
\*  - Initialize the enviromental variables.
\*  - The first transition is a scheduling step.
Scheduler_Init ==   
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) = 0
  /\ timer = [p \in Proc |-> 0]
  /\ subround = "sched"  
  
               

\*  - Initialize process variables.
\*  - If a process is crashed, set its time-outs to 0. Otherwise, set 1.          
Proc_Init ==
  /\ pc = [ p \in Proc |-> "send" ]
  /\ existMsgOfAge = [ << p, q >> \in Proc \times Proc |-> [ k \in MsgAge |-> FALSE ]]        
  /\ suspected = [<< p, q >> \in Proc \times Proc |-> FALSE]
  /\ waiting_time = [<< rcver, snder >> \in Proc \times Proc |-> 0 ]
  /\ timeout = [<< p, q >> \in Proc \times Proc |-> 
                    IF pc[p] = "crash" 
                    THEN 0
                    ELSE TODefault ]
  /\ del = [<< p, q >> \in Proc \times Proc |-> FALSE]                  

  
\*  - Initial states 
\*  - Initial states might not satisfy the inductive invariant IndInvInPostfix.
\*  However, for every execution path, there exists a postfix such that every 
\*  state in this postfix satisfies IndInvInPostfix. This property is checked 
\*  with the liveness PostfixIndInv of the specification ESpec which are defined in the
\*  end. Notice that initial states in Spec_EventualIndInv always have F crashes.
Init == Proc_Init /\  Scheduler_Init  

\*  - Schedule the movement of processes. 
\*  - If timer'[i] # 0, process p_i is frozen in the next global transition. 
\*  - If process i is already crashed, then timer[i] = 0.
\*  - In this encoding, a global transition contains four subrounds: schedule, send, 
\*  deliver, and comp whose order is fixed: sched -> send -> del -> comp. 
\*  - A global transition is sometimes called as a big step, and subrounds are called 
\*  small steps. 
Schedule ==  
  /\ subround = "sched"
  /\ subround' = "send"  
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
          /\ timer' = [ p \in Proc |-> IF p \notin aliveProc   
                                             THEN 0 
                                             ELSE IF p \in activeProc
                                                  THEN 0
                                                  ELSE timer[p] + 1]
                                          
       
\* Increase every age by 1. This udpate is done in the "sched" subround.                                                                                    
\* All process variables are unchanged. The ghost variable fromLastSend
\* is updated only here.          
IncMsgAge ==        
  IF Delta = 0
  THEN UNCHANGED  existMsgOfAge
  ELSE /\ existMsgOfAge' \in MsgAgePowerSet
       /\ \A rcver \in Proc : 
              IF pc'[rcver] = "crash" 
              THEN \A snder \in Proc : \A k \in MsgAge : ~existMsgOfAge'[<<snder, rcver>>][k]
              ELSE \A snder \in Proc : \A k \in MsgAge : 
                        IF k = 0
                        THEN ~existMsgOfAge'[<<snder, rcver>>][k]
                        ELSE IF k = Delta
                             THEN existMsgOfAge'[<<snder, rcver>>][Delta] = existMsgOfAge[<<snder, rcver>>][Delta] \/ existMsgOfAge[<<snder, rcver>>][Delta - 1]
                             ELSE existMsgOfAge'[<<snder, rcver>>][k] = existMsgOfAge[<<snder, rcver>>][k - 1]                                    
   
\* Update the configuration because of recently crashed processes.     
UponCrash ==
  /\ timeout' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN 0
                        ELSE timeout[p, q]]
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
\*  the subround "send" can add 0 in message buffers.
\*  - Other variables are unchanged.                                                                                                                                                             
AddNewMsgs ==
  /\ subround = "send"
  /\ subround' = "del" 
  /\ existMsgOfAge' = [ << snder, rcver >> \in Proc \times Proc |-> [ k \in MsgAge |-> 
                          IF pc[rcver] # "crash" /\ pc[snder] = "send" /\ timer[snder] = 0 /\ k = 0
                          THEN TRUE
                          ELSE existMsgOfAge[<<snder, rcver>>][k] ]]   
  /\ UNCHANGED << pc, timer, del >>
     
\* Only increase waiting time  
UponSend ==                
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"   
                            THEN 0
                            ELSE IF /\ pc[p] = "send" 
                                    /\ timer[p] = 0 
                                    /\ waiting_time[p, q] < timeout[p, q]
                                 THEN waiting_time[p, q] + 1
                                 ELSE waiting_time[p, q]]
  /\ UNCHANGED << suspected, timeout >>                           
   
\*  - For every pair of processes <<snder, rcver>>, remove an arbitrary set of 
\*  messages in existMsgOfAge[snder, rcver]. The obtained result must satisfy partially 
\*  synchronous constraints. Messages sent to crashed processes are ignored.
\*  - Set del'[rcver, snder] = existMsgOfAge'[snder, rcver] # existMsgOfAge[snder, rcver] for 
\*  every snder, for every active "del" rcver. We do not need to know what messages 
\*  have been delivered.  
Deliver ==
  /\ subround = "del"
  /\ subround' = "comp"     
  /\ existMsgOfAge' \in MsgAgePowerSet   
  /\ \A snder, rcver \in Proc : 
          IF pc[rcver] = "crash"
          THEN \A k \in MsgAge : ~existMsgOfAge'[<<snder, rcver>>][k] 
          ELSE IF pc[rcver] = "del" /\ timer[rcver] = 0
               THEN /\ ~existMsgOfAge'[<<snder, rcver>>][Delta]
                    /\ \A k \in MsgAge : existMsgOfAge'[<<snder, rcver>>][k] => existMsgOfAge[<<snder, rcver>>][k]                                        
               ELSE \A k \in MsgAge : existMsgOfAge'[<<snder, rcver>>][k] = existMsgOfAge[<<snder, rcver>>][k]                  
  /\ del' = [<< rcver, snder >> \in Proc \times Proc |->
                    IF pc[rcver] = "crash"                                                             
                    THEN FALSE                    
                    ELSE IF pc[rcver] = "del" /\ timer[rcver] = 0 
                         THEN \E k \in MsgAge : existMsgOfAge'[<<snder, rcver>>][k] # existMsgOfAge[<<snder, rcver>>][k]                        
                         ELSE del[rcver, snder] ] 
  /\ UNCHANGED << pc, timer >>                         
  
                      
\*  - If an active rcver has not received any messages from a snder in this step,  
\*  and has waited for snder less than timeout[rcver, snder], then it increases 
\*  waiting_time[rcver, snder] by 1. If waiting-time[rcver, snder] already equals
\*  to time-out[rcver, snder], the waiting time is unchanged. This optimization 
\*  is used to reduced the number of states.
\*  - If received some message from a suspected process, update the prediction,
\*  and increase the timeout.                      
UponReceive ==                                          
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash" 
                            THEN 0
                            ELSE IF pc[p] = "del"/\ timer[p] = 0  
                                 THEN IF del'[p, q] 
                                      THEN 0
                                      ELSE IF waiting_time[p, q] < timeout[p, q] 
                                           THEN waiting_time[p, q] + 1           
                                           ELSE waiting_time[p, q]
                                 ELSE waiting_time[p, q]]      
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                            IF (pc[p] = "crash")   
                            THEN FALSE
                            ELSE IF pc[p] = "del" /\ timer[p] = 0 /\ del'[p, q] /\ suspected[p, q]  
                                 THEN FALSE
                                 ELSE suspected[p, q] ]                                  
  /\ timeout' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"   
                            THEN 0
                            ELSE IF /\ pc[p] = "del" 
                                    /\ timer[p] = 0
                                    /\ suspected[p, q]                                    
                                    /\ ~suspected'[p, q]  
                                 THEN timeout[p, q] + 1
                                 ELSE timeout[p, q]]   
    
      
\*  - If the waiting time equals the time-out, change the predicition.
\*  - Update the waiting time.    
Comp ==
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                      IF pc[p] = "crash"   
                      THEN FALSE
                      ELSE IF /\ pc[p] = "comp" 
                              /\ p # q
                              /\ timer[p] = 0 
                              /\ ~del[p, q] 
                              /\ waiting_time[p, q] = timeout[p, q]  
                           THEN TRUE
                           ELSE suspected[p, q] ]
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"    
                            THEN 0
                            ELSE IF /\ pc[p] = "comp" 
                                    /\ timer[p] = 0 
                                    /\ waiting_time[p, q] < timeout[p, q]
                                    /\ ~suspected'[p, q]
                                 THEN waiting_time[p, q] + 1
                                 ELSE waiting_time[p, q]]
  /\ UNCHANGED << timeout >>                               
  
  
\* Partially synchronous constraint for relative process speed. This constraint
\* is checked in only the scheduling step.          
PhiConstraint == 
  \A i \in Proc : pc'[i] # "crash" => /\ 0 <= timer'[i] 
                                      /\ timer'[i] < Phi
                                  
\* Partially synchronous constraint for message delay. This constraint is checked
\* in only the delivery step.
DeltaConstraint ==
  subround = "del" => 
      (\A rcver \in Proc : 
               (pc[rcver] = "del" /\ timer[rcver] = 0) 
            => (\A snder \in Proc : ~existMsgOfAge'[<<snder, rcver>>][Delta]))   
                                        

\* Constraints on behaviors of crashed processes: their speed, predictions and  
\* upcoming messages can be ignored. Similar to PhiConstraint, this contraint
\* is checked in only the scheduling step.  
CrashConstraint ==
  /\ Cardinality({p \in Proc : pc'[p] = "crash"}) <= F
  /\ \A p \in Proc : 
        pc'[p] = "crash"  
            => /\ timer'[p] = 0
               /\ \A q \in Proc : /\ del'[p, q] = FALSE                                                                    
                                  /\ \A k \in MsgAge : ~existMsgOfAge'[<< q, p >>][k]    
  
\* Transitions                                             
Next == 
  \/ /\ Schedule          \* Mark a subset of Proc as active ones               
     /\ PhiConstraint     \* A new schedule must satisfy Phi and                               
     /\ IncMsgAge       \* Move to a next time point
     /\ UNCHANGED del     \* No delivery in the schedule step
     /\ CrashConstraint   \* Crash constraints              
     /\ UponCrash         \* Only for crashed processes         
  \/ /\ AddNewMsgs        \* New messages appear in the message buffers
     /\ UponSend          \* Only increase wating time        
  \/ /\ Deliver           \* Deliver messages     
     /\ DeltaConstraint   \* Check the Delta constraint        
     /\ UponReceive       \* Update failure detectors based on incoming messages     
  \/ /\ subround = "comp"    \* The environment updates only the variable subround
     /\ subround' = "sched"
     /\ UNCHANGED << existMsgOfAge, del, pc, timer >>
     /\ Comp               


\* Next == UNCHANGED vars 

\* Check only StrongCompleteness and EventualStrongAccuracy with Spec  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ pc \in [Proc -> Action]
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) <= F
  /\ del \in [Proc \times Proc -> BOOLEAN]  
  /\ existMsgOfAge \in [ Proc \times Proc -> [ MsgAge -> BOOLEAN ]]
  /\ subround \in {"sched", "send", "del", "comp"}
  /\ timer \in [Proc -> 0..Phi] 
  /\ waiting_time \in [ Proc \times Proc -> Int]
  /\ suspected \in [Proc \times Proc -> BOOLEAN]  
  /\ timeout \in [ Proc \times Proc -> Int]
  
StrongCompleteness == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] = "crash") => suspected[p, q])

\* There is a time after which correct processes are not suspected by any correct 
\* process. 
EventuallyStrongAccuracy == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash") => ~suspected[p, q])  
  
StrongAccuracy == 
  \A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash") => ~suspected[p, q]
  
Init0 ==
/\  del = (<<1, 1>> :> FALSE)
/\  existMsgOfAge = <<<<(0 :> FALSE @@ 1 :> FALSE)>>>>
/\  pc = <<"del">>
/\  subround = "del"
/\  suspected = (<<1, 1>> :> FALSE)
/\  timeout = (<<1, 1>> :> 7)
/\  timer = <<0>>
/\  waiting_time = (<<1, 1>> :> 0)


  
=============================================================================
\* Modification History
\* Last modified Wed Apr 14 16:07:02 CEST 2021 by tran
\* Last modified Mon Mar 09 19:38:29 CET 2020 by tthai
\* Created Fri Nov 29 14:06:49 CET 2019 by tthai
