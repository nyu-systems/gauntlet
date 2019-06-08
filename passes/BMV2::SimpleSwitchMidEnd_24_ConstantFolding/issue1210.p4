--- dumps/pruned/issue1210-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:31:57.779711500 +0200
+++ dumps/pruned/issue1210-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:57.782532700 +0200
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
