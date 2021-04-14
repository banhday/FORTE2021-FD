# FORTE2021-FD

This repository contains our specifications for the Chandra and Toueg failure detector.
- Folder fd_paras has our TLA+ specifications fd_paras.tla and fd_paras_crashed.tla for the original version of the Chandra and Toueg failure detector. These specifications are parameterized by the number of processes, the initial value of the timeout, the bound Delta of message delay, and the bound Phi of the relative speeds of processes. The main difference is type of variable existMsgOfAge. While existMsgOfAge has type of [ Proc x Proc -> [ MsgAge -> BOOLEAN ]] in fd_paras.tla, it has type of [ Proc -> [ Proc ->  MsgAge -> BOOLEAN ]]] in fd_paras_crashed.tla. This change makes TLC crashed when it checks an instance with 3 processes, 1 crash, Delta = 2 and Phi = 1.
- Folder fd_cutoffs has our specifications when the cutoff results and other encoding techniques described in our report are applied. Our specifications are written in TLA+, FAST, and Ivy.
