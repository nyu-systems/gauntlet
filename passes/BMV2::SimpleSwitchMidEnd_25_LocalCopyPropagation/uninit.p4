--- dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:33.933394000 +0200
+++ dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:33.935891800 +0200
@@ -44,18 +44,12 @@ parser p1(packet_in p, out Header h) {
     }
 }
 control c(out bit<32> v) {
-    bit<32> d_2;
-    bit<32> setByAction;
     bit<32> e;
-    bool touched;
     @name("c.a1") action a1_0() {
-        setByAction = 32w1;
     }
     @name("c.a1") action a1_2() {
-        setByAction = 32w1;
     }
     @name("c.a2") action a2_0() {
-        setByAction = 32w1;
     }
     @name("c.t") table t {
         actions = {
@@ -65,7 +59,6 @@ control c(out bit<32> v) {
         default_action = a1_0();
     }
     apply {
-        d_2 = 32w1;
         if (e > 32w0) 
             e = 32w1;
         else 
@@ -73,7 +66,6 @@ control c(out bit<32> v) {
         e = e + 32w1;
         switch (t.apply().action_run) {
             a1_0: {
-                touched = true;
             }
         }
         if (e > 32w0) 
