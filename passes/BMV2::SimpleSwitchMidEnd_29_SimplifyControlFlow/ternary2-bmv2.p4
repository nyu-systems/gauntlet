--- dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:29.937033000 +0200
+++ dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:30.035756100 +0200
@@ -130,17 +130,15 @@ control ingress(inout packet_t hdrs, ino
     }
     apply {
         test1.apply();
-        {
-            switch (ex1.apply().action_run) {
-                act1_0: {
-                    tbl1.apply();
-                }
-                act2_0: {
-                    tbl2.apply();
-                }
-                act3_0: {
-                    tbl3.apply();
-                }
+        switch (ex1.apply().action_run) {
+            act1_0: {
+                tbl1.apply();
+            }
+            act2_0: {
+                tbl2.apply();
+            }
+            act3_0: {
+                tbl3.apply();
             }
         }
     }
@@ -152,12 +150,10 @@ control egress(inout packet_t hdrs, inou
 control deparser(packet_out b, in packet_t hdrs) {
     apply {
         b.emit<data_h>(hdrs.data);
-        {
-            b.emit<extra_h>(hdrs.extra[0]);
-            b.emit<extra_h>(hdrs.extra[1]);
-            b.emit<extra_h>(hdrs.extra[2]);
-            b.emit<extra_h>(hdrs.extra[3]);
-        }
+        b.emit<extra_h>(hdrs.extra[0]);
+        b.emit<extra_h>(hdrs.extra[1]);
+        b.emit<extra_h>(hdrs.extra[2]);
+        b.emit<extra_h>(hdrs.extra[3]);
     }
 }
 V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
