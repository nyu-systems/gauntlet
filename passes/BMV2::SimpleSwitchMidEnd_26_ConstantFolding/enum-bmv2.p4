--- dumps/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:33.836329500 +0200
+++ dumps/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:33.838063400 +0200
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
