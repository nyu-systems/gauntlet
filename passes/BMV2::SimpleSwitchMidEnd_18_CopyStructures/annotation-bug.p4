--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:29:02.755705200 +0200
+++ dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:29:02.764390000 +0200
@@ -17,7 +17,9 @@ control cc() {
     headers hdr_1;
     headers tmp_0;
     apply {
-        tmp_0 = { hdr_1.ipv4_option_timestamp };
+        {
+            tmp_0.ipv4_option_timestamp = hdr_1.ipv4_option_timestamp;
+        }
         get<headers>(tmp_0);
     }
 }
