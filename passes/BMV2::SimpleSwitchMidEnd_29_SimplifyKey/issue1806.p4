--- before_pass
+++ after_pass
@@ -18,9 +18,10 @@ control c(inout Headers h, inout standar
     }
     @name("c.do_act") action do_act() {
     }
+    bit<10> key_0;
     @name("c.tns") table tns_0 {
         key = {
-            h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
+            key_0: exact @name("h.eth.tst[13:4]") ;
         }
         actions = {
             do_act();
@@ -30,7 +31,10 @@ control c(inout Headers h, inout standar
     }
     apply {
         {
-            tns_0.apply();
+            {
+                key_0 = h.eth.tst[13:4];
+                tns_0.apply();
+            }
         }
     }
 }
