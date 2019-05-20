--- dumps/p4_16_samples/issue1127-bmv2.p4/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:09.383918000 +0200
+++ dumps/p4_16_samples/issue1127-bmv2.p4/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:09.386298100 +0200
@@ -17,50 +17,36 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    h1_t tmp_3_h1;
-    bit<8> tmp_4;
-    h1_t tmp_5_h1;
-    bit<8> tmp_6;
     h1_t hdr_1_h1;
-    bit<8> op;
     apply {
         {
-            tmp_3_h1 = hdr.h1;
         }
-        tmp_4 = hdr.h1.op1;
         {
-            hdr_1_h1 = tmp_3_h1;
+            hdr_1_h1 = hdr.h1;
         }
-        op = tmp_4;
-        if (op == 8w0x0) 
+        if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
-            if (op[7:4] == 4w1) 
+            if (hdr.h1.op1[7:4] == 4w1) 
                 hdr_1_h1.out1 = 8w4;
         {
-            tmp_3_h1 = hdr_1_h1;
         }
         {
-            hdr.h1 = tmp_3_h1;
+            hdr.h1 = hdr_1_h1;
         }
         {
-            tmp_5_h1 = hdr.h1;
         }
-        tmp_6 = hdr.h1.op2;
         {
-            hdr_1_h1 = tmp_5_h1;
         }
-        op = tmp_6;
-        if (op == 8w0x0) 
+        if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
-            if (op[7:4] == 4w1) 
+            if (hdr.h1.op2[7:4] == 4w1) 
                 hdr_1_h1.out1 = 8w4;
         {
-            tmp_5_h1 = hdr_1_h1;
         }
         {
-            hdr.h1 = tmp_5_h1;
+            hdr.h1 = hdr_1_h1;
         }
     }
 }
