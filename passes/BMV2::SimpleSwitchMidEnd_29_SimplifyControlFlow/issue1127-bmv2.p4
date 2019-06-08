--- dumps/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:55.231185300 +0200
+++ dumps/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:55.319408400 +0200
@@ -19,35 +19,19 @@ parser parserI(packet_in pkt, out header
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     h1_t hdr_1_h1;
     apply {
-        {
-        }
-        {
-            hdr_1_h1 = hdr.h1;
-        }
+        hdr_1_h1 = hdr.h1;
         if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
             if (hdr.h1.op1[7:4] == 4w1) 
                 hdr_1_h1.out1 = 8w4;
-        {
-        }
-        {
-            hdr.h1 = hdr_1_h1;
-        }
-        {
-        }
-        {
-        }
+        hdr.h1 = hdr_1_h1;
         if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
             if (hdr.h1.op2[7:4] == 4w1) 
                 hdr_1_h1.out1 = 8w4;
-        {
-        }
-        {
-            hdr.h1 = hdr_1_h1;
-        }
+        hdr.h1 = hdr_1_h1;
     }
 }
 control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
