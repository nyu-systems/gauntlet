--- before_pass
+++ after_pass
@@ -4,7 +4,7 @@ struct switch_metadata_t {
     bit<8> port;
 }
 header serialized_switch_metadata_t {
-    switch_metadata_t meta;
+    bit<8> _meta_port0;
 }
 struct parsed_packet_t {
     serialized_switch_metadata_t mirrored_md;
@@ -20,7 +20,7 @@ control ingress(inout parsed_packet_t h,
     apply {
         h.mirrored_md.setValid();
         {
-            h.mirrored_md.meta.port = 8w0;
+            h.mirrored_md._meta_port0 = 8w0;
         }
     }
 }
