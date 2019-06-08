--- dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:02.578779500 +0200
+++ dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:02.581311100 +0200
@@ -15,12 +15,10 @@ struct tuple_0 {
 extern bit<16> get<T>(in T data);
 control cc() {
     ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
-    ipv4_option_timestamp_t tmp_0_ipv4_option_timestamp;
     apply {
         {
-            tmp_0_ipv4_option_timestamp = hdr_1_ipv4_option_timestamp;
         }
-        get<headers>({ tmp_0_ipv4_option_timestamp });
+        get<headers>({ hdr_1_ipv4_option_timestamp });
     }
 }
 control C();
