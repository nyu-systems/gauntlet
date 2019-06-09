--- before_pass
+++ after_pass
@@ -327,18 +327,19 @@ control ingress(inout headers hdr, inout
     }
 }
 control IngressDeparserImpl(packet_out packet, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd, out psa_ingress_deparser_output_metadata_t ostd) {
-    clone_metadata_t clone_md_0;
+    bit<3> clone_md_0_type;
+    clone_union_t clone_md_0_data;
     apply {
-        clone_md_0.data.h1.setValid();
+        clone_md_0_data.h1.setValid();
         {
-            clone_md_0.data.h1.data = 32w0;
+            clone_md_0_data.h1.data = 32w0;
         }
-        clone_md_0.type = 3w0;
+        clone_md_0_type = 3w0;
         if (meta.custom_clone_id == 3w1) {
-            ostd.clone_metadata.type = clone_md_0.type;
+            ostd.clone_metadata.type = clone_md_0_type;
             {
-                ostd.clone_metadata.data.h0 = clone_md_0.data.h0;
-                ostd.clone_metadata.data.h1 = clone_md_0.data.h1;
+                ostd.clone_metadata.data.h0 = clone_md_0_data.h0;
+                ostd.clone_metadata.data.h1 = clone_md_0_data.h1;
             }
         }
         packet.emit<ethernet_t>(hdr.ethernet);
