model SC_Delta_4_Phi_5 {

var suspected, waitingtime, timeout, sPC, rPC, buf, sTimer, rTimer;

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
    guard := sTimer < 14;
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
    guard := rTimer < 5 - 1;
    action := rTimer' = rTimer + 1;
};


transition IncreaseMsgAge_CaseA := {
    from := rsched;
    to := incMsgAge;
    guard := buf < 16;
    action := buf' = buf + buf;
};

transition IncreaseMsgAge_CaseB := {
    from := rsched;
    to := incMsgAge;
    guard := buf >= 16 && buf < 16 + 8;
    action := buf' = buf + buf - 16;
};

transition IncreaseMsgAge_CaseC := {
    from := rsched;
    to := incMsgAge;
    guard := buf >= 16 + 8;
    action := buf' = buf + buf - 32;
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
transition RRcv_Active_Suspected_3_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_3_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 3 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
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
transition RRcv_Active_Suspected_4_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 4 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_4_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 4 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_5_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_5_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_5_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_5_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_5_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_5_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 5 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_6_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_6_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_6_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_6_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_6_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_6_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 6 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_7_7 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_7_7 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 7 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_8_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 8 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_8_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 8 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_9_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_9_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_9_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_9_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_9_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_9_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 9 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_10_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_10_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_10_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_10_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_10_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_10_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 10 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_11_11 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_11_11 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 11 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_12_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_12_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_12_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_12_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_12_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_12_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 12 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_13_13 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_13_13 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 13 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_14_14 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_14_14 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 14 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 14, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 13, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_3 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_4 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 11, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_5 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_6 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_7 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_7 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_8 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 7, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_9 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_10 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_11 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_11 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_12 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_13 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_13 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_14 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_14 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_15_15 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_15_15 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 15 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_16_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 16 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_16_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 16 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_17_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 17 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_17_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 17 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_17_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 17 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_17_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 17 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_18_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 18 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_18_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 18 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_18_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 18 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_18_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 18 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_19_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_19_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_19_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_19_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_19_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_19_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_19_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_19_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 19 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_20_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 20 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_20_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 20 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_20_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 20 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_20_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 20 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_21_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_21_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_21_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_21_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_21_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_21_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_21_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_21_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 21 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_22_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_22_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_22_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_22_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_22_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_22_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_22_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_22_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 22 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 7, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_23_23 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_23_23 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 23 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_24_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 24 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_24_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 24 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_24_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 24 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_24_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 24 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_25_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_25_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_25_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_25_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_25_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_25_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_25_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_25_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 25 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_26_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_26_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_26_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_26_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_26_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_26_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_26_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_26_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 26 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 11, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_27_27 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_27_27 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 27 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_28_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_28_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_28_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_28_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_28_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_28_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_28_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_28_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 28 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 13, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_29_29 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_29_29 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 29 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 14, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_30_30 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_30_30 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 30 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 15, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_16 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 15, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 14, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_17 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 14, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 13, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_18 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 13, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 12, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_19 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 12, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 11, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_20 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 11, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 10, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_21 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 10, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 9, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_22 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 9, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_23 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 8, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_23 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 8, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 7, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_24 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 7, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 6, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_25 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 6, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 5, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_26 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 5, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_27 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 4, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_27 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 4, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 3, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_28 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 3, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_29 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 2, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_29 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 2, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_30 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 1, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_30 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 1, waitingtime' = 0;
};
transition RRcv_Active_Suspected_31_31 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 1;
    action := buf' = 0, waitingtime' = 0, suspected' = 0,
                timeout' = timeout + 1;
};
transition RRcv_Active_Unsuspected_31_31 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf = 31 && suspected = 0;
    action := buf' = 0, waitingtime' = 0;
};


transition RRcv_NoDelivery_1 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf < 16 && waitingtime < timeout;
    action := waitingtime' = waitingtime + 1;
};

transition RRcv_NoDelivery_2 := {
    from := rnosnd;
    to := rrcv;
    guard := rTimer = 0 && rPC = 7 && buf < 16 && waitingtime = timeout;
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
    && waitingtime = 0 && timeout = 34 };    

Transitions tNoCrashedSnder := { 
                    SSched_Snd, SSched_Inactive,
                    RSched_NoSnd, RSched_Rcv, RSched_Comp, RSched_Inactive,
                    IncreaseMsgAge_CaseA, IncreaseMsgAge_CaseB, IncreaseMsgAge_CaseC,
                    SSnd_Active, SSnd_Inactive,
                    RNoSnd_Active_CaseA, RNoSnd_Active_CaseB, RNoSnd_Inactive,
                    RRcv_Active_Suspected_1_1, RRcv_Active_Unsuspected_1_1, RRcv_Active_Suspected_2_2, RRcv_Active_Unsuspected_2_2, RRcv_Active_Suspected_3_1, RRcv_Active_Unsuspected_3_1, RRcv_Active_Suspected_3_2, RRcv_Active_Unsuspected_3_2, RRcv_Active_Suspected_3_3, RRcv_Active_Unsuspected_3_3, RRcv_Active_Suspected_4_4, RRcv_Active_Unsuspected_4_4, RRcv_Active_Suspected_5_1, RRcv_Active_Unsuspected_5_1, RRcv_Active_Suspected_5_4, RRcv_Active_Unsuspected_5_4, RRcv_Active_Suspected_5_5, RRcv_Active_Unsuspected_5_5, RRcv_Active_Suspected_6_2, RRcv_Active_Unsuspected_6_2, RRcv_Active_Suspected_6_4, RRcv_Active_Unsuspected_6_4, RRcv_Active_Suspected_6_6, RRcv_Active_Unsuspected_6_6, RRcv_Active_Suspected_7_1, RRcv_Active_Unsuspected_7_1, RRcv_Active_Suspected_7_2, RRcv_Active_Unsuspected_7_2, RRcv_Active_Suspected_7_3, RRcv_Active_Unsuspected_7_3, RRcv_Active_Suspected_7_4, RRcv_Active_Unsuspected_7_4, RRcv_Active_Suspected_7_5, RRcv_Active_Unsuspected_7_5, RRcv_Active_Suspected_7_6, RRcv_Active_Unsuspected_7_6, RRcv_Active_Suspected_7_7, RRcv_Active_Unsuspected_7_7, RRcv_Active_Suspected_8_8, RRcv_Active_Unsuspected_8_8, RRcv_Active_Suspected_9_1, RRcv_Active_Unsuspected_9_1, RRcv_Active_Suspected_9_8, RRcv_Active_Unsuspected_9_8, RRcv_Active_Suspected_9_9, RRcv_Active_Unsuspected_9_9, RRcv_Active_Suspected_10_2, RRcv_Active_Unsuspected_10_2, RRcv_Active_Suspected_10_8, RRcv_Active_Unsuspected_10_8, RRcv_Active_Suspected_10_10, RRcv_Active_Unsuspected_10_10, RRcv_Active_Suspected_11_1, RRcv_Active_Unsuspected_11_1, RRcv_Active_Suspected_11_2, RRcv_Active_Unsuspected_11_2, RRcv_Active_Suspected_11_3, RRcv_Active_Unsuspected_11_3, RRcv_Active_Suspected_11_8, RRcv_Active_Unsuspected_11_8, RRcv_Active_Suspected_11_9, RRcv_Active_Unsuspected_11_9, RRcv_Active_Suspected_11_10, RRcv_Active_Unsuspected_11_10, RRcv_Active_Suspected_11_11, RRcv_Active_Unsuspected_11_11, RRcv_Active_Suspected_12_4, RRcv_Active_Unsuspected_12_4, RRcv_Active_Suspected_12_8, RRcv_Active_Unsuspected_12_8, RRcv_Active_Suspected_12_12, RRcv_Active_Unsuspected_12_12, RRcv_Active_Suspected_13_1, RRcv_Active_Unsuspected_13_1, RRcv_Active_Suspected_13_4, RRcv_Active_Unsuspected_13_4, RRcv_Active_Suspected_13_5, RRcv_Active_Unsuspected_13_5, RRcv_Active_Suspected_13_8, RRcv_Active_Unsuspected_13_8, RRcv_Active_Suspected_13_9, RRcv_Active_Unsuspected_13_9, RRcv_Active_Suspected_13_12, RRcv_Active_Unsuspected_13_12, RRcv_Active_Suspected_13_13, RRcv_Active_Unsuspected_13_13, RRcv_Active_Suspected_14_2, RRcv_Active_Unsuspected_14_2, RRcv_Active_Suspected_14_4, RRcv_Active_Unsuspected_14_4, RRcv_Active_Suspected_14_6, RRcv_Active_Unsuspected_14_6, RRcv_Active_Suspected_14_8, RRcv_Active_Unsuspected_14_8, RRcv_Active_Suspected_14_10, RRcv_Active_Unsuspected_14_10, RRcv_Active_Suspected_14_12, RRcv_Active_Unsuspected_14_12, RRcv_Active_Suspected_14_14, RRcv_Active_Unsuspected_14_14, RRcv_Active_Suspected_15_1, RRcv_Active_Unsuspected_15_1, RRcv_Active_Suspected_15_2, RRcv_Active_Unsuspected_15_2, RRcv_Active_Suspected_15_3, RRcv_Active_Unsuspected_15_3, RRcv_Active_Suspected_15_4, RRcv_Active_Unsuspected_15_4, RRcv_Active_Suspected_15_5, RRcv_Active_Unsuspected_15_5, RRcv_Active_Suspected_15_6, RRcv_Active_Unsuspected_15_6, RRcv_Active_Suspected_15_7, RRcv_Active_Unsuspected_15_7, RRcv_Active_Suspected_15_8, RRcv_Active_Unsuspected_15_8, RRcv_Active_Suspected_15_9, RRcv_Active_Unsuspected_15_9, RRcv_Active_Suspected_15_10, RRcv_Active_Unsuspected_15_10, RRcv_Active_Suspected_15_11, RRcv_Active_Unsuspected_15_11, RRcv_Active_Suspected_15_12, RRcv_Active_Unsuspected_15_12, RRcv_Active_Suspected_15_13, RRcv_Active_Unsuspected_15_13, RRcv_Active_Suspected_15_14, RRcv_Active_Unsuspected_15_14, RRcv_Active_Suspected_15_15, RRcv_Active_Unsuspected_15_15, RRcv_Active_Suspected_16_16, RRcv_Active_Unsuspected_16_16, RRcv_Active_Suspected_17_16, RRcv_Active_Unsuspected_17_16, RRcv_Active_Suspected_17_17, RRcv_Active_Unsuspected_17_17, RRcv_Active_Suspected_18_16, RRcv_Active_Unsuspected_18_16, RRcv_Active_Suspected_18_18, RRcv_Active_Unsuspected_18_18, RRcv_Active_Suspected_19_16, RRcv_Active_Unsuspected_19_16, RRcv_Active_Suspected_19_17, RRcv_Active_Unsuspected_19_17, RRcv_Active_Suspected_19_18, RRcv_Active_Unsuspected_19_18, RRcv_Active_Suspected_19_19, RRcv_Active_Unsuspected_19_19, RRcv_Active_Suspected_20_16, RRcv_Active_Unsuspected_20_16, RRcv_Active_Suspected_20_20, RRcv_Active_Unsuspected_20_20, RRcv_Active_Suspected_21_16, RRcv_Active_Unsuspected_21_16, RRcv_Active_Suspected_21_17, RRcv_Active_Unsuspected_21_17, RRcv_Active_Suspected_21_20, RRcv_Active_Unsuspected_21_20, RRcv_Active_Suspected_21_21, RRcv_Active_Unsuspected_21_21, RRcv_Active_Suspected_22_16, RRcv_Active_Unsuspected_22_16, RRcv_Active_Suspected_22_18, RRcv_Active_Unsuspected_22_18, RRcv_Active_Suspected_22_20, RRcv_Active_Unsuspected_22_20, RRcv_Active_Suspected_22_22, RRcv_Active_Unsuspected_22_22, RRcv_Active_Suspected_23_16, RRcv_Active_Unsuspected_23_16, RRcv_Active_Suspected_23_17, RRcv_Active_Unsuspected_23_17, RRcv_Active_Suspected_23_18, RRcv_Active_Unsuspected_23_18, RRcv_Active_Suspected_23_19, RRcv_Active_Unsuspected_23_19, RRcv_Active_Suspected_23_20, RRcv_Active_Unsuspected_23_20, RRcv_Active_Suspected_23_21, RRcv_Active_Unsuspected_23_21, RRcv_Active_Suspected_23_22, RRcv_Active_Unsuspected_23_22, RRcv_Active_Suspected_23_23, RRcv_Active_Unsuspected_23_23, RRcv_Active_Suspected_24_16, RRcv_Active_Unsuspected_24_16, RRcv_Active_Suspected_24_24, RRcv_Active_Unsuspected_24_24, RRcv_Active_Suspected_25_16, RRcv_Active_Unsuspected_25_16, RRcv_Active_Suspected_25_17, RRcv_Active_Unsuspected_25_17, RRcv_Active_Suspected_25_24, RRcv_Active_Unsuspected_25_24, RRcv_Active_Suspected_25_25, RRcv_Active_Unsuspected_25_25, RRcv_Active_Suspected_26_16, RRcv_Active_Unsuspected_26_16, RRcv_Active_Suspected_26_18, RRcv_Active_Unsuspected_26_18, RRcv_Active_Suspected_26_24, RRcv_Active_Unsuspected_26_24, RRcv_Active_Suspected_26_26, RRcv_Active_Unsuspected_26_26, RRcv_Active_Suspected_27_16, RRcv_Active_Unsuspected_27_16, RRcv_Active_Suspected_27_17, RRcv_Active_Unsuspected_27_17, RRcv_Active_Suspected_27_18, RRcv_Active_Unsuspected_27_18, RRcv_Active_Suspected_27_19, RRcv_Active_Unsuspected_27_19, RRcv_Active_Suspected_27_24, RRcv_Active_Unsuspected_27_24, RRcv_Active_Suspected_27_25, RRcv_Active_Unsuspected_27_25, RRcv_Active_Suspected_27_26, RRcv_Active_Unsuspected_27_26, RRcv_Active_Suspected_27_27, RRcv_Active_Unsuspected_27_27, RRcv_Active_Suspected_28_16, RRcv_Active_Unsuspected_28_16, RRcv_Active_Suspected_28_20, RRcv_Active_Unsuspected_28_20, RRcv_Active_Suspected_28_24, RRcv_Active_Unsuspected_28_24, RRcv_Active_Suspected_28_28, RRcv_Active_Unsuspected_28_28, RRcv_Active_Suspected_29_16, RRcv_Active_Unsuspected_29_16, RRcv_Active_Suspected_29_17, RRcv_Active_Unsuspected_29_17, RRcv_Active_Suspected_29_20, RRcv_Active_Unsuspected_29_20, RRcv_Active_Suspected_29_21, RRcv_Active_Unsuspected_29_21, RRcv_Active_Suspected_29_24, RRcv_Active_Unsuspected_29_24, RRcv_Active_Suspected_29_25, RRcv_Active_Unsuspected_29_25, RRcv_Active_Suspected_29_28, RRcv_Active_Unsuspected_29_28, RRcv_Active_Suspected_29_29, RRcv_Active_Unsuspected_29_29, RRcv_Active_Suspected_30_16, RRcv_Active_Unsuspected_30_16, RRcv_Active_Suspected_30_18, RRcv_Active_Unsuspected_30_18, RRcv_Active_Suspected_30_20, RRcv_Active_Unsuspected_30_20, RRcv_Active_Suspected_30_22, RRcv_Active_Unsuspected_30_22, RRcv_Active_Suspected_30_24, RRcv_Active_Unsuspected_30_24, RRcv_Active_Suspected_30_26, RRcv_Active_Unsuspected_30_26, RRcv_Active_Suspected_30_28, RRcv_Active_Unsuspected_30_28, RRcv_Active_Suspected_30_30, RRcv_Active_Unsuspected_30_30, RRcv_Active_Suspected_31_16, RRcv_Active_Unsuspected_31_16, RRcv_Active_Suspected_31_17, RRcv_Active_Unsuspected_31_17, RRcv_Active_Suspected_31_18, RRcv_Active_Unsuspected_31_18, RRcv_Active_Suspected_31_19, RRcv_Active_Unsuspected_31_19, RRcv_Active_Suspected_31_20, RRcv_Active_Unsuspected_31_20, RRcv_Active_Suspected_31_21, RRcv_Active_Unsuspected_31_21, RRcv_Active_Suspected_31_22, RRcv_Active_Unsuspected_31_22, RRcv_Active_Suspected_31_23, RRcv_Active_Unsuspected_31_23, RRcv_Active_Suspected_31_24, RRcv_Active_Unsuspected_31_24, RRcv_Active_Suspected_31_25, RRcv_Active_Unsuspected_31_25, RRcv_Active_Suspected_31_26, RRcv_Active_Unsuspected_31_26, RRcv_Active_Suspected_31_27, RRcv_Active_Unsuspected_31_27, RRcv_Active_Suspected_31_28, RRcv_Active_Unsuspected_31_28, RRcv_Active_Suspected_31_29, RRcv_Active_Unsuspected_31_29, RRcv_Active_Suspected_31_30, RRcv_Active_Unsuspected_31_30, RRcv_Active_Suspected_31_31, RRcv_Active_Unsuspected_31_31, 
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






