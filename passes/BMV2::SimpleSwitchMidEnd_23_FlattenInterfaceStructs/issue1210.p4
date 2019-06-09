--- before_pass
+++ after_pass
@@ -6,8 +6,8 @@ struct PortId_t {
 struct parsed_headers_t {
 }
 struct metadata_t {
-    PortId_t foo;
-    PortId_t bar;
+    bit<9> _foo__v0;
+    bit<9> _bar__v1;
 }
 parser ParserImpl(packet_in packet, out parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     state start {
@@ -16,10 +16,10 @@ parser ParserImpl(packet_in packet, out
 }
 control IngressImpl(inout parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     apply {
-        if (true && meta.foo._v == meta.bar._v) 
-            meta.foo._v = meta.foo._v + 9w1;
-        if (true && meta.foo._v == 9w192) 
-            meta.foo._v = meta.foo._v + 9w1;
+        if (true && meta._foo__v0 == meta._bar__v1) 
+            meta._foo__v0 = meta._foo__v0 + 9w1;
+        if (true && meta._foo__v0 == 9w192) 
+            meta._foo__v0 = meta._foo__v0 + 9w1;
     }
 }
 control EgressImpl(inout parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
