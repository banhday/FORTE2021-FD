model SC_Delta_0 {

var phi, suspected, waitingtime, timeout, sPC, rPC, buf, sTimer, rTimer, loc;

states normal;


transition SSched_Snd := {
    from := normal;
    to := normal;
    guard := loc = 2 && 1 < sTimer;
    action := loc' = 3, sTimer' = 0;
};

transition SSched_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 2 && sTimer < phi + phi + phi - 1;
    action := loc' = 3, sTimer' = sTimer + 1;
};


transition RSched_NoSnd := {
    from := normal;
    to := normal;
    guard := loc = 3 && rPC = 8;
    action := loc' = 4, rPC' = 6, rTimer' = 0;
};

transition RSched_Rcv := {
    from := normal;
    to := normal;
    guard := loc = 3 && rPC = 6;
    action := loc' = 4, rPC' = 7, rTimer' = 0;
};

transition RSched_Comp := {
    from := normal;
    to := normal;
    guard := loc = 3 && rPC = 7;
    action := loc' = 4, rPC' = 8, rTimer' = 0;
};

transition RSched_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 3 && rTimer < phi - 1;
    action := loc' = 4, rTimer' = rTimer + 1;
};


transition IncreaseMsgAge := {
    from := normal;
    to := normal;
    guard := loc = 4;
    action := loc' = 5;
};



transition SSnd_Active := {
    from := normal;
    to := normal;
    guard := loc = 5 && sTimer = 0 && sPC = 7;
    action := loc' = 6, buf' = 1;
};



transition SSnd_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 5 && !(sTimer = 0 && sPC = 5);
    action := loc' = 6, buf' = buf;
};


transition RNoSnd_Active_CaseA := {
    from := normal;
    to := normal;
    guard := loc = 6 && rTimer = 0 && rPC = 6 && waitingtime < timeout;
    action := loc' = 7, waitingtime' = waitingtime + 1;
};

transition RNoSnd_Active_CaseB := {
    from := normal;
    to := normal;
    guard := loc = 6 && rTimer = 0 && rPC = 6 && waitingtime = timeout;
    action := loc' = 7;
};


transition RNoSnd_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 6 && !(rTimer = 0 && rPC = 6);
    action := loc' = 7;
};

transition RRcv_Active_Suspected_11 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};


transition RRcv_NoDelivery_1 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 1 && waitingtime < timeout;
    action := loc' = 8, waitingtime' = waitingtime + 1;
};

transition RRcv_NoDelivery_2 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 1 && waitingtime = timeout;
    action := loc' = 8;
};

transition RRcv_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 7 && !(rTimer = 0 && rPC = 10);
    action := loc' = 8;
};



transition RComp_CaseA := {
    from := normal;
    to := normal;
    guard := loc = 8 && rTimer = 0 && rPC = 8 
                && suspected = 0 && waitingtime < timeout;
    action := loc' = 2, waitingtime' = waitingtime + 1;
};

transition RComp_CaseB := {
    from := normal;
    to := normal;
    guard := loc = 8 && rTimer = 0 && rPC = 8 
                && suspected = 0 && waitingtime = timeout;
    action := loc' = 2, suspected' = 1;
};

transition RComp_CaseC := {
    from := normal;
    to := normal;
    guard := loc = 8 && rTimer = 0 && rPC = 8 
                && suspected = 1 && waitingtime = timeout;
    action := loc' = 2;
};

transition RComp_Inactive := {
    from := normal;
    to := normal;
    guard := loc = 8 && !(rTimer = 0 && rPC = 8);
    action := loc' = 2;
};

}

strategy SA_BigTimeout  {

Region init := { state = normal && sTimer = 0 && rTimer = 0 
    && sPC = 5 && rPC = 8 && buf = 0 && suspected = 0
    && waitingtime = 0 && loc = 2 && timeout = phi + phi + phi + phi + phi + phi + 0 };    

Transitions tNoCrashedSnder := { 
                    SSched_Snd, SSched_Inactive,
                    RSched_NoSnd, RSched_Rcv, RSched_Comp, RSched_Inactive,
                    IncreaseMsgAge,
                    SSnd_Active, SSnd_Inactive,
                    RNoSnd_Active_CaseA, RNoSnd_Active_CaseB, RNoSnd_Inactive,
                    RRcv_Active_Suspected_11, RRcv_Active_Unsuspected_11, 
                    RRcv_NoDelivery_1, RRcv_NoDelivery_1, RRcv_Inactive,
                    RComp_CaseA, RComp_CaseB, RComp_CaseC, RComp_Inactive
                     };

Region reach := 
                post*(init, tNoCrashedSnder);


Region rightTrust := { state = normal && suspected = 0 };

boolean testStrongAccuracy := 
            subSet(reach, rightTrust);

if testStrongAccuracy
then print("HOLDS");
else print("NOT HOLDS");
endif

}






