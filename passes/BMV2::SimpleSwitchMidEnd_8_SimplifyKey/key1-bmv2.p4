--- before_pass
+++ after_pass
@@ -38,9 +38,10 @@ control ingress(inout Headers h, inout M
     @name("ingress.c.a") action c_a_0() {
         h.h.b = h.h.a;
     }
+    bit<32> key_0;
     @name("ingress.c.t") table c_t {
         key = {
-            h.h.a + 32w1: exact @name("e") ;
+            key_0: exact @name("e") ;
         }
         actions = {
             c_a_0();
@@ -49,7 +50,10 @@ control ingress(inout Headers h, inout M
         default_action = NoAction_0();
     }
     apply {
-        c_t.apply();
+        {
+            key_0 = h.h.a + 32w1;
+            c_t.apply();
+        }
         sm.egress_spec = 9w0;
     }
 }
