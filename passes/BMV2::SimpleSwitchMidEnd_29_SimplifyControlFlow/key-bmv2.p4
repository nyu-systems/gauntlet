--- dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:20.025819700 +0200
+++ dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:20.096037400 +0200
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
