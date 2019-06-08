--- before_pass
+++ after_pass
@@ -14,8 +14,6 @@ bit<32> test_func() {
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     @name("IngressImpl.update_value") action update_value_0() {
-        {
-        }
     }
     apply {
         test_func();
