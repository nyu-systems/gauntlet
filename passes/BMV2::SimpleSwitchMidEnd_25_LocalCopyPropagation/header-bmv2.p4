--- dumps/pruned/header-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:45.372052600 +0200
+++ dumps/pruned/header-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:45.375994600 +0200
@@ -32,10 +32,8 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    hdr c_tmp_0;
     apply {
-        c_tmp_0.f = h.h.f + 32w1;
-        h.h.f = c_tmp_0.f;
+        h.h.f = h.h.f + 32w1;
         sm.egress_spec = 9w0;
     }
 }
