--- dumps/pruned/issue891-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:44.552996700 +0200
+++ dumps/pruned/issue891-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:44.585447000 +0200
@@ -32,16 +32,14 @@ control MyComputeChecksum(inout my_packe
 }
 control MyDeparser(packet_out b, in my_packet p) {
     apply {
-        {
-            b.emit<mpls>(p.data[0]);
-            b.emit<mpls>(p.data[1]);
-            b.emit<mpls>(p.data[2]);
-            b.emit<mpls>(p.data[3]);
-            b.emit<mpls>(p.data[4]);
-            b.emit<mpls>(p.data[5]);
-            b.emit<mpls>(p.data[6]);
-            b.emit<mpls>(p.data[7]);
-        }
+        b.emit<mpls>(p.data[0]);
+        b.emit<mpls>(p.data[1]);
+        b.emit<mpls>(p.data[2]);
+        b.emit<mpls>(p.data[3]);
+        b.emit<mpls>(p.data[4]);
+        b.emit<mpls>(p.data[5]);
+        b.emit<mpls>(p.data[6]);
+        b.emit<mpls>(p.data[7]);
     }
 }
 V1Switch<my_packet, my_metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
