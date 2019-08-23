--- before_pass
+++ after_pass
@@ -17,10 +17,16 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop(inout standard_metadata_t smeta) {
+    bit<16> tmp;
+    bit<16> x_0;
+    bool hasReturned;
+    bit<16> retval;
+    standard_metadata_t smeta;
+    @name(".my_drop") action my_drop() {
+        smeta = standard_metadata;
         mark_to_drop(smeta);
+        standard_metadata = smeta;
     }
-    bit<16> tmp;
     @name("ingress.set_port") action set_port(bit<9> output_port) {
         standard_metadata.egress_spec = output_port;
     }
@@ -30,16 +36,15 @@ control ingress(inout headers hdr, inout
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
-            bit<16> x_0 = hdr.ethernet.srcAddr[15:0];
-            bool hasReturned = false;
-            bit<16> retval;
+            x_0 = hdr.ethernet.srcAddr[15:0];
+            hasReturned = false;
             if (x_0 > 16w5) {
                 hasReturned = true;
                 retval = x_0 + 16w65535;
