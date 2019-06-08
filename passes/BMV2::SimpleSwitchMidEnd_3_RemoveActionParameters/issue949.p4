--- dumps/pruned/issue949-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:49.491202000 +0200
+++ dumps/pruned/issue949-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:49.506451000 +0200
@@ -38,9 +38,9 @@ control egress(inout headers hdr, inout
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+    bool tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bool tmp_0;
     @name("ingress.setDest") action setDest_0() {
         hdr.ethernet.dstAddr = 48w0x6af3400426d3;
     }
