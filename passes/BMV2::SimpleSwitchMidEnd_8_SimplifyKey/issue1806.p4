--- before_pass
+++ after_pass
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
