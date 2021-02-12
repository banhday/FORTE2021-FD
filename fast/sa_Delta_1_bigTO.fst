model SC_Delta_1 {

var suspected, waitingtime, timeout, sPC, rPC, buf, sTimer, rTimer, phi;

states ssched, rsched, incMsgAge, ssnd, rnosnd, rrcv, rcomp;


transition SSched_Snd := {
    from := rcomp;
    to := ssched;
    guard := 1 < sTimer;
    action := sTimer' = 0;
};

transition SSched_Inactive := {
    from := rcomp;
    to := ssched;
    guard := sTimer < phi + phi + phi - 1;
    action := sTimer' = sTimer + 1;
};


transition RSched_NoSnd := {
    from := ssched;
    to := rsched;
    guard := rPC = 8;
    action := rPC' = 6, rTimer' = 0;
};

transition RSched_Rcv := {
    from := ssched;
    to := rsched;
    guard := rPC = 6;
    action := rPC' = 7, rTimer' = 0;
};

transition RSched_Comp := {
    from := ssched;
    to := rsched;
    guard := rPC = 7;
    action := rPC' = 8, rTimer' = 0;
};

transition RSched_Inactive := {
    from := ssched;
    to := rsched;
    guard := rTimer < phi - 1;
    action := rTimer' = rTimer + 1;
};


transition IncreaseMsgAge_CaseA := {
    from := rsched;
    to := incMsgAge;
    guard := buf < 2;
    action := buf' = buf + buf;
};

transition IncreaseMsgAge_CaseB := {
    from := rsched;
    to := incMsgAge;
    guard := buf >= 2 && buf < 2 + 1;
    action := buf' = buf + buf - 2;
};

transition IncreaseMsgAge_CaseC := {
    from := rsched;
    to := incMsgAge;
    guard := buf >= 2 + 1;
    action := buf' = buf + buf - 4;
};





transition SSnd_Active := {
    from := incMsgAge;
    to := ssnd;
    guard := sTimer = 0 && sPC = 5;
    action := buf' = buf + 1;
};



transition SSnd_Inactive := {
    from := incMsgAge;
    to := ssnd;
    guard := !(sTimer = 0 && sPC = 5);
    action := buf' = buf;
};


transition RNoSnd_Active_CaseA := {
    from := ssnd;
    to := rnosnd;
    guard := rTimer = 0 && rPC = 6 && waitingtime < timeout;
    action := waitingtime' = waitingtime + 1;
};

transition RNoSnd_Active_CaseB := {
    from := ssnd;
    to := rnosnd;
    guard := rTimer = 0 && rPC = 6 && waitingtime = timeout;
    action := buf' = buf;
};


transition RNoSnd_Inactive := {
    from := ssnd;
    to := rnosnd;
    guard := !(rTimer = 0 && rPC = 6);
    action := buf' = buf;
};

transition RRcv_Active_Suspected_1_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 1 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 1 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 2 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 2 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};


transition RRcv_NoDelivery_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf < 2 && waitingtime < timeout;
    action := waitingtime' = waitingtime + 1;
};

transition RRcv_NoDelivery_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf < 2 && waitingtime = timeout;
    action := buf' = buf;
};

transition RRcv_Inactive := {
    from := rnosnd;
    to := rrcv;
    guard := !(rTimer = 0 && rPC = 7);
    action := buf' = buf;
};



transition RComp_CaseA := {
    from := rrcv;
    to := rcomp;
    guard := rTimer = 0 && rPC = 8 
                && suspected = 0 && waitingtime < timeout;
    action := waitingtime' = waitingtime + 1;
};

transition RComp_CaseB := {
    from := rrcv;
    to := rcomp;
    guard := rTimer = 0 && rPC = 8 
                && suspected = 0 && waitingtime = timeout;
    action := suspected' = 1;
};

transition RComp_CaseC := {
    from := rrcv;
    to := rcomp;
    guard := rTimer = 0 && rPC = 8 
                && suspected = 1 && waitingtime = timeout;
    action := buf' = buf;
};

transition RComp_Inactive := {
    from := rrcv;
    to := rcomp;
    guard := !(rTimer = 0 && rPC = 8);
    action := buf' = buf;
};

}

strategy SA_BigTimeout  {

Region init := { state = rcomp && sTimer = 0 && rTimer = 0 
    && sPC = 5 && rPC = 8 && buf = 0 && suspected = 0
    && waitingtime = 0 && timeout = phi + phi + phi + phi + phi + phi + 1 };    

Transitions tNoCrashedSnder := { 
                    SSched_Snd, SSched_Inactive,
                    RSched_NoSnd, RSched_Rcv, RSched_Comp, RSched_Inactive,
                    IncreaseMsgAge_CaseA, IncreaseMsgAge_CaseB, IncreaseMsgAge_CaseC,
                    SSnd_Active, SSnd_Inactive,
                    RNoSnd_Active_CaseA, RNoSnd_Active_CaseB, RNoSnd_Inactive,
                    RRcv_Active_Suspected_1_1, RRcv_Active_Unsuspected_1_1, RRcv_Active_Suspected_2_2, RRcv_Active_Unsuspected_2_2, RRcv_Active_Suspected_3_2, RRcv_Active_Unsuspected_3_2, RRcv_Active_Suspected_3_3, RRcv_Active_Unsuspected_3_3, 
                    RRcv_NoDelivery_1, RRcv_NoDelivery_1, RRcv_Inactive,
                    RComp_CaseA, RComp_CaseB, RComp_CaseC, RComp_Inactive
                     };

Region reach := 
                post*(init, tNoCrashedSnder);


Region rightTrust := { suspected = 0 };

boolean testStrongAccuracy := 
            subSet(reach, rightTrust);

if testStrongAccuracy
then print("HOLDS");
else print("NOT HOLDS");
endif

}






