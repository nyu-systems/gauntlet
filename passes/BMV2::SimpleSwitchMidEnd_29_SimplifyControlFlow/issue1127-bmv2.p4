--- before_pass
+++ after_pass
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
