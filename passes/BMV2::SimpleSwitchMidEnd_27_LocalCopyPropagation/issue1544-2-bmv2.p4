--- before_pass
+++ after_pass
@@ -17,10 +17,6 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<16> tmp;
-    bit<16> x_0;
-    bool hasReturned;
-    bit<16> retval;
     bit<16> tmp_0;
     standard_metadata_t smeta;
     @name(".my_drop") action my_drop() {
@@ -90,16 +86,11 @@ control ingress(inout headers hdr, inout
     apply {
         mac_da_0.apply();
         {
-            x_0 = hdr.ethernet.srcAddr[15:0];
-            hasReturned = false;
-            tmp_0 = x_0;
-            if (x_0 > 16w5) 
-                tmp_0 = x_0 + 16w65535;
-            hasReturned = true;
-            retval = tmp_0;
-            tmp = retval;
+            tmp_0 = hdr.ethernet.srcAddr[15:0];
+            if (hdr.ethernet.srcAddr[15:0] > 16w5) 
+                tmp_0 = hdr.ethernet.srcAddr[15:0] + 16w65535;
         }
-        hdr.ethernet.srcAddr[15:0] = tmp;
+        hdr.ethernet.srcAddr[15:0] = tmp_0;
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
