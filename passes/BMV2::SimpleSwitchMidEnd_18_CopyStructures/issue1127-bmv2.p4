--- dumps/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:31:55.195752400 +0200
+++ dumps/pruned/issue1127-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:31:55.200937300 +0200
@@ -24,28 +24,44 @@ control cIngress(inout headers hdr, inou
     headers hdr_1;
     bit<8> op;
     apply {
-        tmp_3 = hdr;
+        {
+            tmp_3.h1 = hdr.h1;
+        }
         tmp_4 = hdr.h1.op1;
-        hdr_1 = tmp_3;
+        {
+            hdr_1.h1 = tmp_3.h1;
+        }
         op = tmp_4;
         if (op == 8w0x0) 
             ;
         else 
             if (op[7:4] == 4w1) 
                 hdr_1.h1.out1 = 8w4;
-        tmp_3 = hdr_1;
-        hdr = tmp_3;
-        tmp_5 = hdr;
+        {
+            tmp_3.h1 = hdr_1.h1;
+        }
+        {
+            hdr.h1 = tmp_3.h1;
+        }
+        {
+            tmp_5.h1 = hdr.h1;
+        }
         tmp_6 = hdr.h1.op2;
-        hdr_1 = tmp_5;
+        {
+            hdr_1.h1 = tmp_5.h1;
+        }
         op = tmp_6;
         if (op == 8w0x0) 
             ;
         else 
             if (op[7:4] == 4w1) 
                 hdr_1.h1.out1 = 8w4;
-        tmp_5 = hdr_1;
-        hdr = tmp_5;
+        {
+            tmp_5.h1 = hdr_1.h1;
+        }
+        {
+            hdr.h1 = tmp_5.h1;
+        }
     }
 }
 control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
