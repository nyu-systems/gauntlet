--- dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:30.321445700 +0200
+++ dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:30.388586200 +0200
@@ -14,8 +14,6 @@ bit<32> test_func() {
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     @name("IngressImpl.update_value") action update_value_0() {
-        {
-        }
     }
     apply {
         test_func();
