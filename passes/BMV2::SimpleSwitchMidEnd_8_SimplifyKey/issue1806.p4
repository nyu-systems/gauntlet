--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 17:30:30.764220000 +0200
+++ dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:30:30.768113800 +0200
@@ -18,9 +18,10 @@ control c(inout Headers h, inout standar
     }
     @name("c.do_act") action do_act_0() {
     }
+    bit<10> key_0;
     @name("c.tns") table tns {
         key = {
-            h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
+            key_0: exact @name("h.eth.tst[13:4]") ;
         }
         actions = {
             do_act_0();
@@ -29,7 +30,10 @@ control c(inout Headers h, inout standar
         default_action = NoAction_0();
     }
     apply {
-        tns.apply();
+        {
+            key_0 = h.eth.tst[13:4];
+            tns.apply();
+        }
     }
 }
 parser p<H>(packet_in _p, out H h);
