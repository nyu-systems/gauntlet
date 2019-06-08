--- dumps/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:53.517143200 +0200
+++ dumps/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:53.563219600 +0200
@@ -50,10 +50,8 @@ control ingress(inout Headers h, inout M
         default_action = NoAction_0();
     }
     apply {
-        {
-            key_0 = h.h.a + h.h.a;
-            c_t_0.apply();
-        }
+        key_0 = h.h.a + h.h.a;
+        c_t_0.apply();
         sm.egress_spec = 9w0;
     }
 }
