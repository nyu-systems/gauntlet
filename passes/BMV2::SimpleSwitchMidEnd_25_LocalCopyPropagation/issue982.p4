--- before_pass
+++ after_pass
@@ -385,16 +385,14 @@ control ingress(inout headers hdr, inout
     }
 }
 control IngressDeparserImpl(packet_out packet, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd, out psa_ingress_deparser_output_metadata_t ostd) {
-    bit<3> clone_md_type;
     clone_union_t clone_md_data;
     apply {
         clone_md_data.h1.setValid();
         {
             clone_md_data.h1.data = 32w0;
         }
-        clone_md_type = 3w0;
         if (meta.custom_clone_id == 3w1) {
-            ostd.clone_metadata.type = clone_md_type;
+            ostd.clone_metadata.type = 3w0;
             {
                 ostd.clone_metadata.data.h0 = clone_md_data.h0;
                 ostd.clone_metadata.data.h1 = clone_md_data.h1;
