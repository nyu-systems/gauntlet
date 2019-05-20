--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:29:02.808052000 +0200
+++ dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:29:02.886265900 +0200
@@ -16,8 +16,6 @@ extern bit<16> get<T>(in T data);
 control cc() {
     ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
     apply {
-        {
-        }
         get<headers>({ hdr_1_ipv4_option_timestamp });
     }
 }
