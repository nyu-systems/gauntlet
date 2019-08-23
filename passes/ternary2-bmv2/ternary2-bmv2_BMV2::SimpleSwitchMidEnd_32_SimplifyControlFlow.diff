--- before_pass
+++ after_pass
@@ -131,20 +131,16 @@ control ingress(inout packet_t hdrs, ino
     }
     apply {
         test1_0.apply();
-        {
-            {
-                key_0 = hdrs.extra[0].h;
-                switch (ex1_0.apply().action_run) {
-                    act1: {
-                        tbl1_0.apply();
-                    }
-                    act2: {
-                        tbl2_0.apply();
-                    }
-                    act3: {
-                        tbl3_0.apply();
-                    }
-                }
+        key_0 = hdrs.extra[0].h;
+        switch (ex1_0.apply().action_run) {
+            act1: {
+                tbl1_0.apply();
+            }
+            act2: {
+                tbl2_0.apply();
+            }
+            act3: {
+                tbl3_0.apply();
             }
         }
     }
@@ -156,12 +152,10 @@ control egress(inout packet_t hdrs, inou
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
