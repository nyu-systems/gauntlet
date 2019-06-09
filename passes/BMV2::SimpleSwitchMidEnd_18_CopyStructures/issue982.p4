--- before_pass
+++ after_pass
@@ -330,10 +330,17 @@ control IngressDeparserImpl(packet_out p
     clone_metadata_t clone_md_0;
     apply {
         clone_md_0.data.h1.setValid();
-        clone_md_0.data.h1 = {32w0};
+        {
+            clone_md_0.data.h1.data = 32w0;
+        }
         clone_md_0.type = 3w0;
-        if (meta.custom_clone_id == 3w1) 
-            ostd.clone_metadata = clone_md_0;
+        if (meta.custom_clone_id == 3w1) {
+            ostd.clone_metadata.type = clone_md_0.type;
+            {
+                ostd.clone_metadata.data.h0 = clone_md_0.data.h0;
+                ostd.clone_metadata.data.h1 = clone_md_0.data.h1;
+            }
+        }
         packet.emit<ethernet_t>(hdr.ethernet);
         packet.emit<ipv4_t>(hdr.ipv4);
     }
