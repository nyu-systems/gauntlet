--- before_pass
+++ after_pass
@@ -16,9 +16,9 @@ parser ParserImpl(packet_in packet, out
 }
 control IngressImpl(inout parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     apply {
-        if (true && meta.foo._v == meta.bar._v) 
+        if (meta.foo._v == meta.bar._v) 
             meta.foo._v = meta.foo._v + 9w1;
-        if (true && meta.foo._v == 9w192) 
+        if (meta.foo._v == 9w192) 
             meta.foo._v = meta.foo._v + 9w1;
     }
 }
