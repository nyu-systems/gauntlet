--- dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:18.361742000 +0200
+++ dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:18.365389000 +0200
@@ -44,19 +44,15 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_first_h2 {
-        {
-            hdr_1_h1 = hdr.h1;
-            hdr_1_h2 = hdr.h2;
-            hdr_1_h3 = hdr.h3;
-        }
+        hdr_1_h1 = hdr.h1;
+        hdr_1_h2 = hdr.h2;
+        hdr_1_h3 = hdr.h3;
         pkt.extract<h2_t>(hdr_1_h2.next);
         verify(hdr_1_h2.last.hdr_type == 8w2, error.BadHeaderType);
         ret_next_hdr_type = hdr_1_h2.last.next_hdr_type;
-        {
-            hdr.h1 = hdr_1_h1;
-            hdr.h2 = hdr_1_h2;
-            hdr.h3 = hdr_1_h3;
-        }
+        hdr.h1 = hdr_1_h1;
+        hdr.h2 = hdr_1_h2;
+        hdr.h3 = hdr_1_h3;
         my_next_hdr_type = ret_next_hdr_type;
         transition select(my_next_hdr_type) {
             8w2: parse_other_h2;
@@ -109,13 +105,11 @@ control uc(inout headers hdr, inout meta
 control DeparserI(packet_out packet, in headers hdr) {
     apply {
         packet.emit<h1_t>(hdr.h1);
-        {
-            packet.emit<h2_t>(hdr.h2[0]);
-            packet.emit<h2_t>(hdr.h2[1]);
-            packet.emit<h2_t>(hdr.h2[2]);
-            packet.emit<h2_t>(hdr.h2[3]);
-            packet.emit<h2_t>(hdr.h2[4]);
-        }
+        packet.emit<h2_t>(hdr.h2[0]);
+        packet.emit<h2_t>(hdr.h2[1]);
+        packet.emit<h2_t>(hdr.h2[2]);
+        packet.emit<h2_t>(hdr.h2[3]);
+        packet.emit<h2_t>(hdr.h2[4]);
         packet.emit<h3_t>(hdr.h3);
     }
 }
