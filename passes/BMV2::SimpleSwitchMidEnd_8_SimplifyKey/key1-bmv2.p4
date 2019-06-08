--- dumps/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-06-08 18:32:54.554313100 +0200
+++ dumps/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-06-08 18:32:54.557021600 +0200
@@ -38,9 +38,10 @@ control ingress(inout Headers h, inout M
     @name("ingress.c.a") action c_a() {
         h.h.b = h.h.a;
     }
+    bit<32> key_0;
     @name("ingress.c.t") table c_t_0 {
         key = {
-            h.h.a + 32w1: exact @name("e") ;
+            key_0: exact @name("e") ;
         }
         actions = {
             c_a();
@@ -49,7 +50,10 @@ control ingress(inout Headers h, inout M
         default_action = NoAction_0();
     }
     apply {
-        c_t_0.apply();
+        {
+            key_0 = h.h.a + 32w1;
+            c_t_0.apply();
+        }
         sm.egress_spec = 9w0;
     }
 }
