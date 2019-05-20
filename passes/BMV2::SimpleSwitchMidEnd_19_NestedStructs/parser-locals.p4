--- dumps/p4_16_samples/parser-locals.p4/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:31:30.120469300 +0200
+++ dumps/p4_16_samples/parser-locals.p4/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 17:31:30.123041100 +0200
@@ -9,10 +9,12 @@ struct S {
     bit<32> c;
 }
 parser p() {
-    S s;
+    H s_h1;
+    H s_h2;
+    bit<32> s_c;
     state start {
-        s.h1.setInvalid();
-        s.h2.setInvalid();
+        s_h1.setInvalid();
+        s_h2.setInvalid();
         transition accept;
     }
 }
