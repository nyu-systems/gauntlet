--- before_pass
+++ after_pass
@@ -12,55 +12,18 @@ struct headers {
     ethernet_t ethernet;
 }
 parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<16> tmp_port_0;
-    bit<16> tmp;
-    bit<16> tmp_0;
-    bit<16> x_0;
-    bool hasReturned;
-    bit<16> retval;
-    bit<16> x_1;
-    bool hasReturned_0;
-    bit<16> retval_0;
     state start {
         {
-            x_0 = (bit<16>)standard_metadata.ingress_port;
-            hasReturned = false;
-            hasReturned = true;
-            retval = x_0 + 16w1;
-            tmp = retval;
         }
-        tmp_port_0 = tmp;
         packet.extract<ethernet_t>(hdr.ethernet);
         {
-            x_1 = hdr.ethernet.etherType;
-            hasReturned_0 = false;
-            hasReturned_0 = true;
-            retval_0 = x_1 + 16w1;
-            tmp_0 = retval_0;
         }
-        hdr.ethernet.etherType = tmp_0;
-        meta.tmp_port = tmp_port_0;
+        hdr.ethernet.etherType = hdr.ethernet.etherType + 16w1;
+        meta.tmp_port = (bit<16>)standard_metadata.ingress_port + 16w1;
         transition accept;
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<16> tmp_1;
-    bit<16> tmp_2;
-    bit<16> tmp_3;
-    bit<16> x_2;
-    bool hasReturned_3;
-    bit<16> retval_3;
-    bit<16> tmp_4;
-    bit<16> tmp_5;
-    bit<16> x_3;
-    bool hasReturned_4;
-    bit<16> retval_4;
-    bit<16> x_4;
-    bool hasReturned_5;
-    bit<16> retval_5;
-    bit<16> x_5;
-    bool hasReturned_6;
-    bit<16> retval_6;
     standard_metadata_t smeta;
     @name(".my_drop") action my_drop() {
         {
@@ -128,38 +91,9 @@ control ingress(inout headers hdr, inout
     }
     apply {
         mac_da_0.apply();
-        {
-            x_2 = hdr.ethernet.srcAddr[15:0];
-            hasReturned_3 = false;
-            {
-                x_3 = x_2;
-                hasReturned_4 = false;
-                hasReturned_4 = true;
-                retval_4 = x_3 + 16w1;
-                tmp_4 = retval_4;
-            }
-            tmp_5 = x_2 + tmp_4;
-            hasReturned_3 = true;
-            retval_3 = tmp_5;
-            tmp_1 = retval_3;
-        }
-        hdr.ethernet.srcAddr[15:0] = tmp_1;
-        {
-            x_4 = hdr.ethernet.srcAddr[15:0];
-            hasReturned_5 = false;
-            hasReturned_5 = true;
-            retval_5 = x_4 + 16w1;
-            tmp_2 = retval_5;
-        }
-        hdr.ethernet.srcAddr[15:0] = tmp_2;
-        {
-            x_5 = hdr.ethernet.etherType;
-            hasReturned_6 = false;
-            hasReturned_6 = true;
-            retval_6 = x_5 + 16w1;
-            tmp_3 = retval_6;
-        }
-        hdr.ethernet.etherType = tmp_3;
+        hdr.ethernet.srcAddr[15:0] = hdr.ethernet.srcAddr[15:0] + (hdr.ethernet.srcAddr[15:0] + 16w1);
+        hdr.ethernet.srcAddr[15:0] = hdr.ethernet.srcAddr[15:0] + 16w1;
+        hdr.ethernet.etherType = hdr.ethernet.etherType + 16w1;
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
