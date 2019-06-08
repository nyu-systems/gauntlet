--- dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:31:50.783817800 +0200
+++ dumps/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:50.785754600 +0200
@@ -25,10 +25,18 @@ control ComputeChecksumI(inout H hdr, in
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     H hdr_1;
     apply {
-        hdr_1 = hdr;
-        hdr = hdr_1;
-        hdr_1 = hdr;
-        hdr = hdr_1;
+        {
+            hdr_1.stack = hdr.stack;
+        }
+        {
+            hdr.stack = hdr_1.stack;
+        }
+        {
+            hdr_1.stack = hdr.stack;
+        }
+        {
+            hdr.stack = hdr_1.stack;
+        }
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
