--- before_pass
+++ after_pass
@@ -93,9 +93,10 @@ control ingress(inout packet_t hdrs, ino
         }
         default_action = noop();
     }
+    bit<16> key_0;
     @name("ingress.ex1") table ex1_0 {
         key = {
-            hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
+            key_0: ternary @name("hdrs.extra[0].h") ;
         }
         actions = {
             setbyte();
@@ -138,15 +139,18 @@ control ingress(inout packet_t hdrs, ino
     }
     apply {
         test1_0.apply();
-        switch (ex1_0.apply().action_run) {
-            act1: {
-                tbl1_0.apply();
-            }
-            act2: {
-                tbl2_0.apply();
-            }
-            act3: {
-                tbl3_0.apply();
+        {
+            key_0 = hdrs.extra[0].h;
+            switch (ex1_0.apply().action_run) {
+                act1: {
+                    tbl1_0.apply();
+                }
+                act2: {
+                    tbl2_0.apply();
+                }
+                act3: {
+                    tbl3_0.apply();
+                }
             }
         }
     }
