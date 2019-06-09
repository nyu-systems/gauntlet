--- before_pass
+++ after_pass
@@ -17,9 +17,6 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<16> tmp;
-    bit<16> x_0;
-    bool hasReturned;
     bit<16> retval;
     standard_metadata_t smeta;
     @name(".my_drop") action my_drop() {
@@ -89,19 +86,14 @@ control ingress(inout headers hdr, inout
     apply {
         mac_da_0.apply();
         {
-            x_0 = hdr.ethernet.srcAddr[15:0];
-            hasReturned = false;
-            if (x_0 > 16w5) {
-                hasReturned = true;
-                retval = x_0 + 16w65535;
+            if (hdr.ethernet.srcAddr[15:0] > 16w5) {
+                retval = hdr.ethernet.srcAddr[15:0] + 16w65535;
             }
             else {
-                hasReturned = true;
-                retval = x_0;
+                retval = hdr.ethernet.srcAddr[15:0];
             }
-            tmp = retval;
         }
-        hdr.ethernet.srcAddr[15:0] = tmp;
+        hdr.ethernet.srcAddr[15:0] = retval;
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
