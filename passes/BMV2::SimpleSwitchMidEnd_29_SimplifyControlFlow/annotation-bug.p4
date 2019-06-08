--- dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:02.592923200 +0200
+++ dumps/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:02.634661800 +0200
@@ -16,8 +16,6 @@ extern bit<16> get<T>(in T data);
 control cc() {
     ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
     apply {
-        {
-        }
         get<headers>({ hdr_1_ipv4_option_timestamp });
     }
 }
