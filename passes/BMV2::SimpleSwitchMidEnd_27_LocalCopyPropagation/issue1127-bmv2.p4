--- before_pass
+++ after_pass
@@ -17,50 +17,26 @@ parser parserI(packet_in pkt, out header
     }
 }
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    h1_t tmp_h1;
-    bit<8> tmp_0;
-    h1_t tmp_1_h1;
-    bit<8> tmp_2;
     h1_t hdr_0_h1;
-    bit<8> op_0;
     apply {
         {
-            tmp_h1 = hdr.h1;
+            hdr_0_h1 = hdr.h1;
         }
-        tmp_0 = hdr.h1.op1;
-        {
-            hdr_0_h1 = tmp_h1;
-        }
-        op_0 = tmp_0;
-        if (op_0 == 8w0x0) 
+        if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
-            if (op_0[7:4] == 4w1) 
+            if (hdr.h1.op1[7:4] == 4w1) 
                 hdr_0_h1.out1 = 8w4;
         {
-            tmp_h1 = hdr_0_h1;
-        }
-        {
-            hdr.h1 = tmp_h1;
-        }
-        {
-            tmp_1_h1 = hdr.h1;
-        }
-        tmp_2 = hdr.h1.op2;
-        {
-            hdr_0_h1 = tmp_1_h1;
+            hdr.h1 = hdr_0_h1;
         }
-        op_0 = tmp_2;
-        if (op_0 == 8w0x0) 
+        if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
-            if (op_0[7:4] == 4w1) 
+            if (hdr.h1.op2[7:4] == 4w1) 
                 hdr_0_h1.out1 = 8w4;
         {
-            tmp_1_h1 = hdr_0_h1;
-        }
-        {
-            hdr.h1 = tmp_1_h1;
+            hdr.h1 = hdr_0_h1;
         }
     }
 }
