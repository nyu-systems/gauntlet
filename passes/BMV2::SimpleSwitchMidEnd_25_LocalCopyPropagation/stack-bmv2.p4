--- dumps/p4_16_samples/stack-bmv2.p4/pruned/stack-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:09.700496200 +0200
+++ dumps/p4_16_samples/stack-bmv2.p4/pruned/stack-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:09.705727500 +0200
@@ -32,10 +32,8 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    hdr[1] c_tmp_0;
     apply {
-        c_tmp_0[0].f = h.h.f + 32w1;
-        h.h.f = c_tmp_0[0].f;
+        h.h.f = h.h.f + 32w1;
         sm.egress_spec = 9w0;
     }
 }
