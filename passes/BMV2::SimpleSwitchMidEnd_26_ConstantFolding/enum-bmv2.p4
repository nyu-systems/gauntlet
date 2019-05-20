--- dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:38.884845200 +0200
+++ dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:38.887971700 +0200
@@ -35,10 +35,7 @@ control deparser(packet_out b, in Header
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     apply {
-        if (32w0 == 32w1) 
-            h.h.c = h.h.a;
-        else 
-            h.h.c = h.h.b;
+        h.h.c = h.h.b;
         sm.egress_spec = 9w0;
     }
 }
