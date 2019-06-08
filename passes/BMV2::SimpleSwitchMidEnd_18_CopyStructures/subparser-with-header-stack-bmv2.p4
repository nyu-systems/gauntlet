--- dumps/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:07.467116900 +0200
+++ dumps/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:07.430992100 +0200
@@ -42,11 +42,19 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_first_h2 {
-        hdr_1 = hdr;
+        {
+            hdr_1.h1 = hdr.h1;
+            hdr_1.h2 = hdr.h2;
+            hdr_1.h3 = hdr.h3;
+        }
         pkt.extract<h2_t>(hdr_1.h2.next);
         verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
         ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
-        hdr = hdr_1;
+        {
+            hdr.h1 = hdr_1.h1;
+            hdr.h2 = hdr_1.h2;
+            hdr.h3 = hdr_1.h3;
+        }
         my_next_hdr_type = ret_next_hdr_type;
         transition select(my_next_hdr_type) {
             8w2: parse_other_h2;
