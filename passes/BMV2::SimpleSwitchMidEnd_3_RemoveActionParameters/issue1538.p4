--- before_pass
+++ after_pass
@@ -15,11 +15,16 @@ parser ParserImpl(packet_in packet, out
     bit<16> tmp_port_0;
     bit<16> tmp;
     bit<16> tmp_0;
+    bit<16> x_0;
+    bool hasReturned;
+    bit<16> retval;
+    bit<16> x_1;
+    bool hasReturned_0;
+    bit<16> retval_0;
     state start {
         {
-            bit<16> x_0 = (bit<16>)standard_metadata.ingress_port;
-            bool hasReturned = false;
-            bit<16> retval;
+            x_0 = (bit<16>)standard_metadata.ingress_port;
+            hasReturned = false;
             hasReturned = true;
             retval = x_0 + 16w1;
             tmp = retval;
@@ -27,9 +32,8 @@ parser ParserImpl(packet_in packet, out
         tmp_port_0 = tmp;
         packet.extract<ethernet_t>(hdr.ethernet);
         {
-            bit<16> x_1 = hdr.ethernet.etherType;
-            bool hasReturned_0 = false;
-            bit<16> retval_0;
+            x_1 = hdr.ethernet.etherType;
+            hasReturned_0 = false;
             hasReturned_0 = true;
             retval_0 = x_1 + 16w1;
             tmp_0 = retval_0;
@@ -40,12 +44,29 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop(inout standard_metadata_t smeta) {
-        mark_to_drop(smeta);
-    }
     bit<16> tmp_1;
     bit<16> tmp_2;
     bit<16> tmp_3;
+    bit<16> x_2;
+    bool hasReturned_3;
+    bit<16> retval_3;
+    bit<16> tmp_4;
+    bit<16> tmp_5;
+    bit<16> x_3;
+    bool hasReturned_4;
+    bit<16> retval_4;
+    bit<16> x_4;
+    bool hasReturned_5;
+    bit<16> retval_5;
+    bit<16> x_5;
+    bool hasReturned_6;
+    bit<16> retval_6;
+    standard_metadata_t smeta;
+    @name(".my_drop") action my_drop() {
+        smeta = standard_metadata;
+        mark_to_drop(smeta);
+        standard_metadata = smeta;
+    }
     @name("ingress.set_port") action set_port(bit<9> output_port) {
         standard_metadata.egress_spec = output_port;
     }
@@ -55,22 +76,18 @@ control ingress(inout headers hdr, inout
         }
         actions = {
             set_port();
-            my_drop(standard_metadata);
+            my_drop();
         }
-        default_action = my_drop(standard_metadata);
+        default_action = my_drop();
     }
     apply {
         mac_da_0.apply();
         {
-            bit<16> x_2 = hdr.ethernet.srcAddr[15:0];
-            bool hasReturned_3 = false;
-            bit<16> retval_3;
-            bit<16> tmp_4;
-            bit<16> tmp_5;
+            x_2 = hdr.ethernet.srcAddr[15:0];
+            hasReturned_3 = false;
             {
-                bit<16> x_3 = x_2;
-                bool hasReturned_4 = false;
-                bit<16> retval_4;
+                x_3 = x_2;
+                hasReturned_4 = false;
                 hasReturned_4 = true;
                 retval_4 = x_3 + 16w1;
                 tmp_4 = retval_4;
@@ -82,18 +99,16 @@ control ingress(inout headers hdr, inout
         }
         hdr.ethernet.srcAddr[15:0] = tmp_1;
         {
-            bit<16> x_4 = hdr.ethernet.srcAddr[15:0];
-            bool hasReturned_5 = false;
-            bit<16> retval_5;
+            x_4 = hdr.ethernet.srcAddr[15:0];
+            hasReturned_5 = false;
             hasReturned_5 = true;
             retval_5 = x_4 + 16w1;
             tmp_2 = retval_5;
         }
         hdr.ethernet.srcAddr[15:0] = tmp_2;
         {
-            bit<16> x_5 = hdr.ethernet.etherType;
-            bool hasReturned_6 = false;
-            bit<16> retval_6;
+            x_5 = hdr.ethernet.etherType;
+            hasReturned_6 = false;
             hasReturned_6 = true;
             retval_6 = x_5 + 16w1;
             tmp_3 = retval_6;
