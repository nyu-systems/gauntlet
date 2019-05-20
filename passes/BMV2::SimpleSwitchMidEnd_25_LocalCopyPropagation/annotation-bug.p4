--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:02.790280400 +0200
+++ dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:02.796462400 +0200
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
