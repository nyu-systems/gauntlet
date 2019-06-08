--- dumps/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:13.624079500 +0200
+++ dumps/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:13.694415800 +0200
@@ -14,8 +14,6 @@ bit<32> test_func() {
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     @name("IngressImpl.update_value") action update_value_0() {
-        {
-        }
     }
     apply {
         test_func();
