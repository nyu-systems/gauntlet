--- before_pass
+++ after_pass
@@ -10,8 +10,9 @@ parser ParserImpl(packet_in packet, out
     }
 }
 bit<32> test_func() {
-    bool hasReturned_0 = false;
+    bool hasReturned_0;
     bit<32> retval_0;
+    hasReturned_0 = false;
     hasReturned_0 = true;
     retval_0 = 32w1;
     return retval_0;
@@ -20,19 +21,22 @@ control IngressImpl(inout headers hdr, i
     bit<32> value_2;
     bit<32> tmp_1;
     bit<32> tmp_2;
-    @name("IngressImpl.update_value") action update_value_0(out bit<32> value_0) {
+    bool hasReturned_1;
+    bit<32> retval_1;
+    bit<32> value_0;
+    @name("IngressImpl.update_value") action update_value_0() {
         {
-            bool hasReturned_1 = false;
-            bit<32> retval_1;
+            hasReturned_1 = false;
             hasReturned_1 = true;
             retval_1 = 32w1;
             tmp_1 = retval_1;
         }
         value_0 = tmp_1;
+        value_2 = value_0;
     }
     apply {
         tmp_2 = test_func();
-        update_value_0(value_2);
+        update_value_0();
     }
 }
 control VerifyChecksumImpl(inout headers hdr, inout metadata meta) {
