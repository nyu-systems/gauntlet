--- dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:59.128763500 +0200
+++ dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:59.131733900 +0200
@@ -19,13 +19,13 @@ control c(out bool b) {
     bool b_3;
     bit<16> bi;
     bit<16> mb;
+    bit<16> bi_1;
+    bit<16> mb_1;
     @name("c.a") action a_0() {
         bi = 16w3;
         mb = -bi;
         xv = mb;
     }
-    bit<16> bi_1;
-    bit<16> mb_1;
     @name("c.a") action a_2() {
         bi_1 = 16w0;
         mb_1 = -bi_1;
