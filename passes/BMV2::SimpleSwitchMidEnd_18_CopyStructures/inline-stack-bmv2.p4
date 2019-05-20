--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:03.735524500 +0200
+++ dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:03.737724700 +0200
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
