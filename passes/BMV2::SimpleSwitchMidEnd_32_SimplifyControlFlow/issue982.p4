--- before_pass
+++ after_pass
@@ -330,15 +330,11 @@ control IngressDeparserImpl(packet_out p
     clone_union_t clone_md_0_data;
     apply {
         clone_md_0_data.h1.setValid();
-        {
-            clone_md_0_data.h1.data = 32w0;
-        }
+        clone_md_0_data.h1.data = 32w0;
         if (meta._custom_clone_id1 == 3w1) {
             ostd.clone_metadata.type = 3w0;
-            {
-                ostd.clone_metadata.data.h0 = clone_md_0_data.h0;
-                ostd.clone_metadata.data.h1 = clone_md_0_data.h1;
-            }
+            ostd.clone_metadata.data.h0 = clone_md_0_data.h0;
+            ostd.clone_metadata.data.h1 = clone_md_0_data.h1;
         }
         packet.emit<ethernet_t>(hdr.ethernet);
         packet.emit<ipv4_t>(hdr.ipv4);
