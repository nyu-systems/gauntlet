--- before_pass
+++ after_pass
@@ -13,25 +13,29 @@ control IngressImpl(inout headers hdr, i
     bit<32> value_0;
     bit<32> tmp;
     bit<32> tmp_0;
-    @name("IngressImpl.update_value") action update_value(out bit<32> value_2) {
+    bool hasReturned;
+    bit<32> retval;
+    bool hasReturned_1;
+    bit<32> retval_1;
+    bit<32> value_2;
+    @name("IngressImpl.update_value") action update_value() {
         {
-            bool hasReturned = false;
-            bit<32> retval;
+            hasReturned = false;
             hasReturned = true;
             retval = 32w1;
             tmp = retval;
         }
         value_2 = tmp;
+        value_0 = value_2;
     }
     apply {
         {
-            bool hasReturned_1 = false;
-            bit<32> retval_1;
+            hasReturned_1 = false;
             hasReturned_1 = true;
             retval_1 = 32w1;
             tmp_0 = retval_1;
         }
-        update_value(value_0);
+        update_value();
     }
 }
 control VerifyChecksumImpl(inout headers hdr, inout metadata meta) {
