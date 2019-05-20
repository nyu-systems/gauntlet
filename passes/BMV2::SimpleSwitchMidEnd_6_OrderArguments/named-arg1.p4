*** dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 16:59:48.195156900 +0200
--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 16:59:48.198398400 +0200
*************** control c(out bool b) {
*** 62,65 ****
  control ce(out bool b);
  parser pe(out bool b);
  package top(pe _p, ce _e, @optional ce _e1);
! top(_e = c(), _p = par()) main;
--- 62,65 ----
  control ce(out bool b);
  parser pe(out bool b);
  package top(pe _p, ce _e, @optional ce _e1);
! top(_p = par(), _e = c()) main;
