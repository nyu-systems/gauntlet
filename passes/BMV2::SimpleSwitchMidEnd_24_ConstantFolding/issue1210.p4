--- dumps/p4_16_samples/issue1210.p4/pruned/issue1210-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:11.679138500 +0200
+++ dumps/p4_16_samples/issue1210.p4/pruned/issue1210-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:11.681700000 +0200
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
