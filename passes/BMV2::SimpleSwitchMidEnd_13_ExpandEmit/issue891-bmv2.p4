--- before_pass
+++ after_pass
@@ -32,7 +32,16 @@ control MyComputeChecksum(inout my_packe
 }
 control MyDeparser(packet_out b, in my_packet p) {
     apply {
-        b.emit<mpls[8]>(p.data);
+        {
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
