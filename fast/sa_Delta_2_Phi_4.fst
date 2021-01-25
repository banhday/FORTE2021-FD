model SC_Delta_{2}_Phi_{4} {

var suspected, waitingtime, timeout, sPC, rPC, buf, sTimer, rTimer, loc;

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
    guard := loc = 2 && sTimer < 11;
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
    guard := loc = 3 && rTimer < 4 - 1;
    action := loc' = 4, rTimer' = rTimer + 1;
};


transition IncreaseMsgAge_CaseA := {
    from := normal;
    to := normal;
    guard := loc = 4 && buf < 4;
    action := loc' = 5, buf' = buf + buf;
};

transition IncreaseMsgAge_CaseB := {
    from := normal;
    to := normal;
    guard := loc = 4 && buf >= 4 && buf < 4 + 2;
    action := loc' = 5, buf' = buf + buf - 4;
};

transition IncreaseMsgAge_CaseC := {
    from := normal;
    to := normal;
    guard := loc = 4 && buf >= 4 + 2;
    action := loc' = 5, buf' = buf + buf - 8;
};





transition SSnd_Active := {
    from := normal;
    to := normal;
    guard := loc = 5 && sTimer = 0 && sPC = 7;
    action := loc' = 6, buf' = buf + 1;
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
transition RRcv_Active_Suspected_22 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 2 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_22 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 3 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_32 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 3 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_32 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_33 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 3 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_33 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_44 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 4 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_44 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_54 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 5 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_54 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_55 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 5 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_55 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_64 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 6 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_64 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_66 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 6 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_66 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_74 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_74 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_75 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_75 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_76 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_76 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_77 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_77 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};


transition RRcv_NoDelivery_1 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 4 && waitingtime < timeout;
    action := loc' = 8, waitingtime' = waitingtime + 1;
};

transition RRcv_NoDelivery_2 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 4 && waitingtime = timeout;
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
    && waitingtime = 0 && loc = 2 && timeout = 26 };    

Transitions tNoCrashedSnder := { 
                    SSched_Snd, SSched_Inactive,
                    RSched_NoSnd, RSched_Rcv, RSched_Comp, RSched_Inactive,
                    IncreaseMsgAge_CaseA, IncreaseMsgAge_CaseB, IncreaseMsgAge_CaseC,
                    SSnd_Active, SSnd_Inactive,
                    RNoSnd_Active_CaseA, RNoSnd_Active_CaseB, RNoSnd_Inactive,
                    RRcv_Active_Suspected_11, RRcv_Active_Unsuspected_11, RRcv_Active_Suspected_22, RRcv_Active_Unsuspected_22, RRcv_Active_Suspected_31, RRcv_Active_Unsuspected_31, RRcv_Active_Suspected_32, RRcv_Active_Unsuspected_32, RRcv_Active_Suspected_33, RRcv_Active_Unsuspected_33, RRcv_Active_Suspected_44, RRcv_Active_Unsuspected_44, RRcv_Active_Suspected_54, RRcv_Active_Unsuspected_54, RRcv_Active_Suspected_55, RRcv_Active_Unsuspected_55, RRcv_Active_Suspected_64, RRcv_Active_Unsuspected_64, RRcv_Active_Suspected_66, RRcv_Active_Unsuspected_66, RRcv_Active_Suspected_74, RRcv_Active_Unsuspected_74, RRcv_Active_Suspected_75, RRcv_Active_Unsuspected_75, RRcv_Active_Suspected_76, RRcv_Active_Unsuspected_76, RRcv_Active_Suspected_77, RRcv_Active_Unsuspected_77, 
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






