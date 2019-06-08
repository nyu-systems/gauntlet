--- dumps/pruned/issue949-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:49.481043400 +0200
+++ dumps/pruned/issue949-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:49.482842700 +0200
@@ -38,7 +38,6 @@ control egress(inout headers hdr, inout
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bool tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.setDest") action setDest_0() {
@@ -55,7 +54,7 @@ control ingress(inout headers hdr, inout
         default_action = NoAction_0();
     }
     apply {
-        tmp_0 = someTable.apply().hit;
+        someTable.apply();
     }
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
