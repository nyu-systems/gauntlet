--- dumps/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:33:04.460950900 +0200
+++ dumps/pruned/parser-locals-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:33:04.464701200 +0200
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
