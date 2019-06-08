--- dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-06-08 18:32:59.176651300 +0200
+++ dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-06-08 18:32:59.179661400 +0200
@@ -62,4 +62,4 @@ control c(out bool b) {
 control ce(out bool b);
 parser pe(out bool b);
 package top(pe _p, ce _e, @optional ce _e1);
-top(_e = c(), _p = par()) main;
+top(_p = par(), _e = c()) main;
