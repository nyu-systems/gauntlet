--- dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:02.555828000 +0200
+++ dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:31:02.558703500 +0200
@@ -14,13 +14,13 @@ struct tuple_0 {
 }
 extern bit<16> get<T>(in T data);
 control cc() {
-    headers hdr_1;
-    headers tmp_0;
+    ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
+    ipv4_option_timestamp_t tmp_0_ipv4_option_timestamp;
     apply {
         {
-            tmp_0.ipv4_option_timestamp = hdr_1.ipv4_option_timestamp;
+            tmp_0_ipv4_option_timestamp = hdr_1_ipv4_option_timestamp;
         }
-        get<headers>(tmp_0);
+        get<headers>({ tmp_0_ipv4_option_timestamp });
     }
 }
 control C();
