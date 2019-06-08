--- dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:31:02.553383900 +0200
+++ dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:02.555828000 +0200
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
