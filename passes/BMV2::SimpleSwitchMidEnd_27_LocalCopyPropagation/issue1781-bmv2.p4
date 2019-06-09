--- before_pass
+++ after_pass
@@ -10,31 +10,9 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<32> value_0;
-    bit<32> tmp;
-    bit<32> tmp_0;
-    bool hasReturned;
-    bit<32> retval;
-    bool hasReturned_1;
-    bit<32> retval_1;
-    bit<32> value_2;
     @name("IngressImpl.update_value") action update_value() {
-        {
-            hasReturned = false;
-            hasReturned = true;
-            retval = 32w1;
-            tmp = retval;
-        }
-        value_2 = tmp;
-        value_0 = value_2;
     }
     apply {
-        {
-            hasReturned_1 = false;
-            hasReturned_1 = true;
-            retval_1 = 32w1;
-            tmp_0 = retval_1;
-        }
         update_value();
     }
 }
