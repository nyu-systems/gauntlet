--- dumps/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:07.430992100 +0200
+++ dumps/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:34:07.432609100 +0200
@@ -30,7 +30,9 @@ struct metadata {
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     bit<8> my_next_hdr_type;
-    headers hdr_1;
+    h1_t hdr_1_h1;
+    h2_t[5] hdr_1_h2;
+    h3_t hdr_1_h3;
     bit<8> ret_next_hdr_type;
     state start {
         pkt.extract<h1_t>(hdr.h1);
@@ -43,17 +45,17 @@ parser parserI(packet_in pkt, out header
     }
     state parse_first_h2 {
         {
-            hdr_1.h1 = hdr.h1;
-            hdr_1.h2 = hdr.h2;
-            hdr_1.h3 = hdr.h3;
+            hdr_1_h1 = hdr.h1;
+            hdr_1_h2 = hdr.h2;
+            hdr_1_h3 = hdr.h3;
         }
-        pkt.extract<h2_t>(hdr_1.h2.next);
-        verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
-        ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
+        pkt.extract<h2_t>(hdr_1_h2.next);
+        verify(hdr_1_h2.last.hdr_type == 8w2, error.BadHeaderType);
+        ret_next_hdr_type = hdr_1_h2.last.next_hdr_type;
         {
-            hdr.h1 = hdr_1.h1;
-            hdr.h2 = hdr_1.h2;
-            hdr.h3 = hdr_1.h3;
+            hdr.h1 = hdr_1_h1;
+            hdr.h2 = hdr_1_h2;
+            hdr.h3 = hdr_1_h3;
         }
         my_next_hdr_type = ret_next_hdr_type;
         transition select(my_next_hdr_type) {
