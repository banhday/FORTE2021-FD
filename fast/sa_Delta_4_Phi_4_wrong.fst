model SC_Delta_4_Phi_4 {

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
    guard := loc = 4 && buf < 16;
    action := loc' = 5, buf' = buf + buf;
};

transition IncreaseMsgAge_CaseB := {
    from := normal;
    to := normal;
    guard := loc = 4 && buf >= 16 && buf < 16 + 8;
    action := loc' = 5, buf' = buf + buf - 16;
};

transition IncreaseMsgAge_CaseC := {
    from := normal;
    to := normal;
    guard := loc = 4 && buf >= 16 + 8;
    action := loc' = 5, buf' = buf + buf - 32;
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
transition RRcv_Active_Suspected_51 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 5 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_51 := {
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
transition RRcv_Active_Suspected_62 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 6 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_62 := {
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
transition RRcv_Active_Suspected_71 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_71 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_72 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_72 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_73 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 7 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_73 := {
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
transition RRcv_Active_Suspected_88 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 8 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_88 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_91 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 9 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_91 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_98 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 9 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_98 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_99 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 9 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_99 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_102 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 10 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_102 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_108 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 10 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_108 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1010 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 10 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1010 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_111 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_111 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_112 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_112 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_113 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_113 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_118 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_118 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_119 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_119 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1110 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1110 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1111 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 11 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1111 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_124 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 12 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_124 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_128 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 12 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_128 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1212 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 12 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1212 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_131 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_131 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_134 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_134 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_135 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_135 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_138 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_138 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_139 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_139 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1312 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1312 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1313 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 13 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1313 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_142 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_142 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_144 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_144 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_146 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_146 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_148 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_148 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1410 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1410 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1412 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1412 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1414 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 14 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1414 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_151 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_151 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_152 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_152 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_153 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_153 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_154 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_154 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_155 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_155 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_156 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_156 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_157 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_157 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_158 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_158 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_159 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_159 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1510 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1510 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1511 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1511 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1512 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1512 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1513 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1513 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1514 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1514 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1515 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 15 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1515 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1616 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 16 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1616 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1716 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 17 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1716 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1717 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 17 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1717 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1816 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 18 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1816 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1818 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 18 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1818 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1916 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 19 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1916 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1917 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 19 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1917 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1918 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 19 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1918 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_1919 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 19 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_1919 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2016 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 20 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2016 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2020 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 20 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2020 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2116 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 21 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2116 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2117 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 21 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2117 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2120 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 21 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2120 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2121 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 21 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2121 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2216 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 22 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2216 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2218 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 22 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2218 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2220 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 22 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2220 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2222 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 22 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2222 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2316 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2316 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2317 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2317 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2318 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2318 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2319 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2319 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2320 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2320 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2321 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2321 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2322 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2322 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2323 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 23 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2323 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2416 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 24 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2416 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2424 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 24 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2424 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2516 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 25 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2516 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2517 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 25 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2517 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2524 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 25 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2524 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2525 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 25 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2525 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2616 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 26 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2616 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2618 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 26 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2618 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2624 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 26 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2624 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2626 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 26 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2626 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2716 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2716 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2717 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2717 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2718 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2718 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2719 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2719 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2724 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2724 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2725 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2725 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2726 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2726 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2727 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 27 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2727 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2816 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 28 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2816 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2820 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 28 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2820 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2824 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 28 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2824 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2828 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 28 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2828 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2916 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2916 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2917 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2917 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2920 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2920 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2921 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2921 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2924 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2924 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2925 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2925 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2928 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2928 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_2929 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 29 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_2929 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3016 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3016 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3018 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3018 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3020 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3020 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3022 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3022 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3024 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3024 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3026 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3026 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3028 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3028 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3030 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 30 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3030 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3116 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 15, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3116 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3117 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3117 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3118 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3118 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3119 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3119 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3120 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3120 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3121 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3121 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3122 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3122 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3123 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3123 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3124 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3124 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3125 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3125 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3126 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3126 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3127 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3127 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3128 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3128 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3129 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3129 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3130 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3130 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_3131 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 31 && suspected = 1;
    action := loc' = 8, buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3131 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf = 1 && suspected = 0;
    action := loc' = 8, buf' = 0, waitingtime' = 0;
};


transition RRcv_NoDelivery_1 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 16 && waitingtime < timeout;
    action := loc' = 8, waitingtime' = waitingtime + 1;
};

transition RRcv_NoDelivery_2 := {
    from := normal;
    to := normal;
    guard := loc = 7 && rTimer = 0 && rPC = 10 && buf < 16 && waitingtime = timeout;
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
    && waitingtime = 0 && loc = 2 && timeout = 5 };    

Transitions tNoCrashedSnder := { 
                    SSched_Snd, SSched_Inactive,
                    RSched_NoSnd, RSched_Rcv, RSched_Comp, RSched_Inactive,
                    IncreaseMsgAge_CaseA, IncreaseMsgAge_CaseB, IncreaseMsgAge_CaseC,
                    SSnd_Active, SSnd_Inactive,
                    RNoSnd_Active_CaseA, RNoSnd_Active_CaseB, RNoSnd_Inactive,
                    RRcv_Active_Suspected_11, RRcv_Active_Unsuspected_11, RRcv_Active_Suspected_22, RRcv_Active_Unsuspected_22, RRcv_Active_Suspected_31, RRcv_Active_Unsuspected_31, RRcv_Active_Suspected_32, RRcv_Active_Unsuspected_32, RRcv_Active_Suspected_33, RRcv_Active_Unsuspected_33, RRcv_Active_Suspected_44, RRcv_Active_Unsuspected_44, RRcv_Active_Suspected_51, RRcv_Active_Unsuspected_51, RRcv_Active_Suspected_54, RRcv_Active_Unsuspected_54, RRcv_Active_Suspected_55, RRcv_Active_Unsuspected_55, RRcv_Active_Suspected_62, RRcv_Active_Unsuspected_62, RRcv_Active_Suspected_64, RRcv_Active_Unsuspected_64, RRcv_Active_Suspected_66, RRcv_Active_Unsuspected_66, RRcv_Active_Suspected_71, RRcv_Active_Unsuspected_71, RRcv_Active_Suspected_72, RRcv_Active_Unsuspected_72, RRcv_Active_Suspected_73, RRcv_Active_Unsuspected_73, RRcv_Active_Suspected_74, RRcv_Active_Unsuspected_74, RRcv_Active_Suspected_75, RRcv_Active_Unsuspected_75, RRcv_Active_Suspected_76, RRcv_Active_Unsuspected_76, RRcv_Active_Suspected_77, RRcv_Active_Unsuspected_77, RRcv_Active_Suspected_88, RRcv_Active_Unsuspected_88, RRcv_Active_Suspected_91, RRcv_Active_Unsuspected_91, RRcv_Active_Suspected_98, RRcv_Active_Unsuspected_98, RRcv_Active_Suspected_99, RRcv_Active_Unsuspected_99, RRcv_Active_Suspected_102, RRcv_Active_Unsuspected_102, RRcv_Active_Suspected_108, RRcv_Active_Unsuspected_108, RRcv_Active_Suspected_1010, RRcv_Active_Unsuspected_1010, RRcv_Active_Suspected_111, RRcv_Active_Unsuspected_111, RRcv_Active_Suspected_112, RRcv_Active_Unsuspected_112, RRcv_Active_Suspected_113, RRcv_Active_Unsuspected_113, RRcv_Active_Suspected_118, RRcv_Active_Unsuspected_118, RRcv_Active_Suspected_119, RRcv_Active_Unsuspected_119, RRcv_Active_Suspected_1110, RRcv_Active_Unsuspected_1110, RRcv_Active_Suspected_1111, RRcv_Active_Unsuspected_1111, RRcv_Active_Suspected_124, RRcv_Active_Unsuspected_124, RRcv_Active_Suspected_128, RRcv_Active_Unsuspected_128, RRcv_Active_Suspected_1212, RRcv_Active_Unsuspected_1212, RRcv_Active_Suspected_131, RRcv_Active_Unsuspected_131, RRcv_Active_Suspected_134, RRcv_Active_Unsuspected_134, RRcv_Active_Suspected_135, RRcv_Active_Unsuspected_135, RRcv_Active_Suspected_138, RRcv_Active_Unsuspected_138, RRcv_Active_Suspected_139, RRcv_Active_Unsuspected_139, RRcv_Active_Suspected_1312, RRcv_Active_Unsuspected_1312, RRcv_Active_Suspected_1313, RRcv_Active_Unsuspected_1313, RRcv_Active_Suspected_142, RRcv_Active_Unsuspected_142, RRcv_Active_Suspected_144, RRcv_Active_Unsuspected_144, RRcv_Active_Suspected_146, RRcv_Active_Unsuspected_146, RRcv_Active_Suspected_148, RRcv_Active_Unsuspected_148, RRcv_Active_Suspected_1410, RRcv_Active_Unsuspected_1410, RRcv_Active_Suspected_1412, RRcv_Active_Unsuspected_1412, RRcv_Active_Suspected_1414, RRcv_Active_Unsuspected_1414, RRcv_Active_Suspected_151, RRcv_Active_Unsuspected_151, RRcv_Active_Suspected_152, RRcv_Active_Unsuspected_152, RRcv_Active_Suspected_153, RRcv_Active_Unsuspected_153, RRcv_Active_Suspected_154, RRcv_Active_Unsuspected_154, RRcv_Active_Suspected_155, RRcv_Active_Unsuspected_155, RRcv_Active_Suspected_156, RRcv_Active_Unsuspected_156, RRcv_Active_Suspected_157, RRcv_Active_Unsuspected_157, RRcv_Active_Suspected_158, RRcv_Active_Unsuspected_158, RRcv_Active_Suspected_159, RRcv_Active_Unsuspected_159, RRcv_Active_Suspected_1510, RRcv_Active_Unsuspected_1510, RRcv_Active_Suspected_1511, RRcv_Active_Unsuspected_1511, RRcv_Active_Suspected_1512, RRcv_Active_Unsuspected_1512, RRcv_Active_Suspected_1513, RRcv_Active_Unsuspected_1513, RRcv_Active_Suspected_1514, RRcv_Active_Unsuspected_1514, RRcv_Active_Suspected_1515, RRcv_Active_Unsuspected_1515, RRcv_Active_Suspected_1616, RRcv_Active_Unsuspected_1616, RRcv_Active_Suspected_1716, RRcv_Active_Unsuspected_1716, RRcv_Active_Suspected_1717, RRcv_Active_Unsuspected_1717, RRcv_Active_Suspected_1816, RRcv_Active_Unsuspected_1816, RRcv_Active_Suspected_1818, RRcv_Active_Unsuspected_1818, RRcv_Active_Suspected_1916, RRcv_Active_Unsuspected_1916, RRcv_Active_Suspected_1917, RRcv_Active_Unsuspected_1917, RRcv_Active_Suspected_1918, RRcv_Active_Unsuspected_1918, RRcv_Active_Suspected_1919, RRcv_Active_Unsuspected_1919, RRcv_Active_Suspected_2016, RRcv_Active_Unsuspected_2016, RRcv_Active_Suspected_2020, RRcv_Active_Unsuspected_2020, RRcv_Active_Suspected_2116, RRcv_Active_Unsuspected_2116, RRcv_Active_Suspected_2117, RRcv_Active_Unsuspected_2117, RRcv_Active_Suspected_2120, RRcv_Active_Unsuspected_2120, RRcv_Active_Suspected_2121, RRcv_Active_Unsuspected_2121, RRcv_Active_Suspected_2216, RRcv_Active_Unsuspected_2216, RRcv_Active_Suspected_2218, RRcv_Active_Unsuspected_2218, RRcv_Active_Suspected_2220, RRcv_Active_Unsuspected_2220, RRcv_Active_Suspected_2222, RRcv_Active_Unsuspected_2222, RRcv_Active_Suspected_2316, RRcv_Active_Unsuspected_2316, RRcv_Active_Suspected_2317, RRcv_Active_Unsuspected_2317, RRcv_Active_Suspected_2318, RRcv_Active_Unsuspected_2318, RRcv_Active_Suspected_2319, RRcv_Active_Unsuspected_2319, RRcv_Active_Suspected_2320, RRcv_Active_Unsuspected_2320, RRcv_Active_Suspected_2321, RRcv_Active_Unsuspected_2321, RRcv_Active_Suspected_2322, RRcv_Active_Unsuspected_2322, RRcv_Active_Suspected_2323, RRcv_Active_Unsuspected_2323, RRcv_Active_Suspected_2416, RRcv_Active_Unsuspected_2416, RRcv_Active_Suspected_2424, RRcv_Active_Unsuspected_2424, RRcv_Active_Suspected_2516, RRcv_Active_Unsuspected_2516, RRcv_Active_Suspected_2517, RRcv_Active_Unsuspected_2517, RRcv_Active_Suspected_2524, RRcv_Active_Unsuspected_2524, RRcv_Active_Suspected_2525, RRcv_Active_Unsuspected_2525, RRcv_Active_Suspected_2616, RRcv_Active_Unsuspected_2616, RRcv_Active_Suspected_2618, RRcv_Active_Unsuspected_2618, RRcv_Active_Suspected_2624, RRcv_Active_Unsuspected_2624, RRcv_Active_Suspected_2626, RRcv_Active_Unsuspected_2626, RRcv_Active_Suspected_2716, RRcv_Active_Unsuspected_2716, RRcv_Active_Suspected_2717, RRcv_Active_Unsuspected_2717, RRcv_Active_Suspected_2718, RRcv_Active_Unsuspected_2718, RRcv_Active_Suspected_2719, RRcv_Active_Unsuspected_2719, RRcv_Active_Suspected_2724, RRcv_Active_Unsuspected_2724, RRcv_Active_Suspected_2725, RRcv_Active_Unsuspected_2725, RRcv_Active_Suspected_2726, RRcv_Active_Unsuspected_2726, RRcv_Active_Suspected_2727, RRcv_Active_Unsuspected_2727, RRcv_Active_Suspected_2816, RRcv_Active_Unsuspected_2816, RRcv_Active_Suspected_2820, RRcv_Active_Unsuspected_2820, RRcv_Active_Suspected_2824, RRcv_Active_Unsuspected_2824, RRcv_Active_Suspected_2828, RRcv_Active_Unsuspected_2828, RRcv_Active_Suspected_2916, RRcv_Active_Unsuspected_2916, RRcv_Active_Suspected_2917, RRcv_Active_Unsuspected_2917, RRcv_Active_Suspected_2920, RRcv_Active_Unsuspected_2920, RRcv_Active_Suspected_2921, RRcv_Active_Unsuspected_2921, RRcv_Active_Suspected_2924, RRcv_Active_Unsuspected_2924, RRcv_Active_Suspected_2925, RRcv_Active_Unsuspected_2925, RRcv_Active_Suspected_2928, RRcv_Active_Unsuspected_2928, RRcv_Active_Suspected_2929, RRcv_Active_Unsuspected_2929, RRcv_Active_Suspected_3016, RRcv_Active_Unsuspected_3016, RRcv_Active_Suspected_3018, RRcv_Active_Unsuspected_3018, RRcv_Active_Suspected_3020, RRcv_Active_Unsuspected_3020, RRcv_Active_Suspected_3022, RRcv_Active_Unsuspected_3022, RRcv_Active_Suspected_3024, RRcv_Active_Unsuspected_3024, RRcv_Active_Suspected_3026, RRcv_Active_Unsuspected_3026, RRcv_Active_Suspected_3028, RRcv_Active_Unsuspected_3028, RRcv_Active_Suspected_3030, RRcv_Active_Unsuspected_3030, RRcv_Active_Suspected_3116, RRcv_Active_Unsuspected_3116, RRcv_Active_Suspected_3117, RRcv_Active_Unsuspected_3117, RRcv_Active_Suspected_3118, RRcv_Active_Unsuspected_3118, RRcv_Active_Suspected_3119, RRcv_Active_Unsuspected_3119, RRcv_Active_Suspected_3120, RRcv_Active_Unsuspected_3120, RRcv_Active_Suspected_3121, RRcv_Active_Unsuspected_3121, RRcv_Active_Suspected_3122, RRcv_Active_Unsuspected_3122, RRcv_Active_Suspected_3123, RRcv_Active_Unsuspected_3123, RRcv_Active_Suspected_3124, RRcv_Active_Unsuspected_3124, RRcv_Active_Suspected_3125, RRcv_Active_Unsuspected_3125, RRcv_Active_Suspected_3126, RRcv_Active_Unsuspected_3126, RRcv_Active_Suspected_3127, RRcv_Active_Unsuspected_3127, RRcv_Active_Suspected_3128, RRcv_Active_Unsuspected_3128, RRcv_Active_Suspected_3129, RRcv_Active_Unsuspected_3129, RRcv_Active_Suspected_3130, RRcv_Active_Unsuspected_3130, RRcv_Active_Suspected_3131, RRcv_Active_Unsuspected_3131, 
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
else print("NOT HOLD");
endif

}






