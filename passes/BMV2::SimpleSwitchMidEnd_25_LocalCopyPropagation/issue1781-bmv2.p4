--- dumps/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:13.607585200 +0200
+++ dumps/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:13.612367300 +0200
@@ -10,32 +10,15 @@ parser ParserImpl(packet_in packet, out
     }
 }
 bit<32> test_func() {
-    bool hasReturned_0;
-    bit<32> retval_0;
-    hasReturned_0 = false;
-    hasReturned_0 = true;
-    retval_0 = 32w1;
-    return retval_0;
+    return 32w1;
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<32> value_2;
-    bit<32> tmp_1;
-    bit<32> tmp_2;
-    bool hasReturned_1;
-    bit<32> retval_1;
-    bit<32> value_0;
     @name("IngressImpl.update_value") action update_value_0() {
         {
-            hasReturned_1 = false;
-            hasReturned_1 = true;
-            retval_1 = 32w1;
-            tmp_1 = retval_1;
         }
-        value_0 = tmp_1;
-        value_2 = value_0;
     }
     apply {
-        tmp_2 = test_func();
+        test_func();
         update_value_0();
     }
 }
