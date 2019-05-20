--- dumps/p4_16_samples/issue887.p4/pruned/issue887-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:31:09.208448200 +0200
+++ dumps/p4_16_samples/issue887.p4/pruned/issue887-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:09.212329600 +0200
@@ -31,8 +31,16 @@ control MyComputeChecksum(inout my_packe
 }
 control MyDeparser(packet_out b, in my_packet p) {
     apply {
-        if (p.data[0].isValid()) 
-            b.emit<mpls[8]>(p.data);
+        if (p.data[0].isValid()) {
+            b.emit<mpls>(p.data[0]);
+            b.emit<mpls>(p.data[1]);
+            b.emit<mpls>(p.data[2]);
+            b.emit<mpls>(p.data[3]);
+            b.emit<mpls>(p.data[4]);
+            b.emit<mpls>(p.data[5]);
+            b.emit<mpls>(p.data[6]);
+            b.emit<mpls>(p.data[7]);
+        }
     }
 }
 V1Switch<my_packet, my_metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
